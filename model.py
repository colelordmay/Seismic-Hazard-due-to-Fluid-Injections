### FLUID FLOW AND RUPTURE MODEL IN SIMPLEST FORM
### Site failures are checked first, then fluid flows
### This is implemented on a dynamic grid, so boundary conditions are never a concern.
### To reproduce simulations with the same number of statistics as in the paper, be prepared to run some of the parameter sweeps for multiple months
### During this time, keep an eye on the RAM. The fracture arrays are emptied every 10000 steps, but a dynamic grid means that 100s of millions of sties will be stored,
###        each with their own pressure and with random heterogeneity
### Generating statistics for this paper required RAM in excess of 100GB.


### Code alternates between two processes: finding sites that fail, and advancing fluid flow.
### All sites will fail first, then when "stability" is reached, the fluid field advances, universally increasing pressure
### New sites are found to be broken

### Some notes when running this code:
### This code does not use numpy. I'm not convinced it would speed it up.
### A lower s_max makes the code slower
### Higher s_max makes the code faster, but very memory intensive.
### MUST compile with pypy (was written when pypy didn't work well with numpy). Speedup is a much needed order of magnitude.

### @Author: Cole Lord-May. clordmay@eoas.ubc.ca
### Published in Seismic hazard due to fluid injections, PHYSICAL REVIEW RESEARCH 2, 043324 (2020)


import random
import bisect
from collections import deque
from random import randrange
import pickle
import os.path
import copy
import operator
import logging
import time
import csv

### This isn't really needed, but this code doesn't use numpy so it can be compiled easily with pypy3
### I'm unsure how well pypy3 works with linux now, but 4 years ago it was troublesome and I never explored other options.
def fastest_argmax(array):
    array = list( array )
    return array.index(max(array))



class bond_network:
    def __init__(self):
        self.vertices={}
        self.distance={}
        self.pressure={}
    def add_vertex(self,name,bond):
        self.vertices.setdefault(name,[]).append(bond)
    def remove_vertex(self,name,to_delete):
        for idx,val in enumerate(self.vertices[name]):
            if to_delete in val:
                del self.vertices[name][idx]
                if len(self.vertices[name])==0:
                    del self.vertices[name]
                break
    
    def update_distance(self,name,position):
        self.distance[name]=position
        
    def update_pressure(self,name,press):
        self.pressure[name]=press

def bi_dict_add(d,a,b):
    d.setdefault(a,[]).append(b)
    d.setdefault(b,[]).append(a)
    return d

def centroid(xarr,yarr):
    length = len(xarr)
    return sum(xarr)/length, sum(yarr)/length



def breaks_loopless(iterations,delta_p,s_min,s_max,tau_max):
    ### Data is saved in these arrays
    total_slips=[]
    area_size=[]
    save_linit=[]
    save_lmax=[]
    in_out_markers=[]
    rt_plot_mech=[]
    rt_plot_t=[]
    energy_rel=[]

    ### injection site
    x,y=0,0

    g_f=bond_network()
    r1,r2,r3,r4=random.random(),random.random(),random.random(),random.random()
    d_f={r1:(0,0),r2:(0,0),r3:(0,0),r4:(0,0)} # Origins of permeability breakage dictionary
    
    ### d_tau and d_s are dictionaries that store tau and s values at all sites. Updated on-the-fly for speed
    d_tau={(0,0):random.random()}
    d_s={(0,0):random.uniform(s_min,s_max)}
    broken_b=set()
    
    ### g_f is for fluid flow. It contains a dictionary of dictionaries that also stores distances from the injection site
    g_f.add_vertex((0,0),{(0,1):r1})
    g_f.add_vertex((0,0),{(0,-1):r2})
    g_f.add_vertex((0,0),{(1,0):r3})
    g_f.add_vertex((0,0),{(-1,0):r4})
    g_f.update_distance((0,0),0)

    ### To speed up locating the site to fail. 
    ### Keeps track of sites in a sorted list in shells (all sites 0,1,2,3... steps away from injection site)
    ### This way the code only has to look at the first element of each sorted list in L_dict to find the site to break.
    ### L_dict_backwards just speeds up backwards referencing.
    L_dict={0:sorted([r1,r2,r3,r4])}
    L_dict_backwards={r1:0,r2:0,r3:0,r4:0}
    graph_f={}
    path={(x,y)}
    
    l_max=1
    l_max_previous=0
    event_counter=0
    
    thresh=10000
    i=-1
    while event_counter<iterations:
        i+=1

### SITE FAILURES ### 
        
        ### First, check if fluid front advances
        if l_max!=l_max_previous: 

            ### Pick which pressure profile you want!
            ### Options are exponential, linear, and inverse, all starting at (0,1) and going to (l_max,delta_p)
            p_list=[delta_p**(float(l)/float(l_max)) for l in range(0,l_max+1)] #Exponential
            #p_list=[1- (1-delta_p)/l_max*l for l in range(0,l_max+1)] #Linear
            #p_list=[1/((1-delta_p)/(l_max*delta_p)*l+1) for l in range(0,l_max+1)] #Inverse
            
            
            ### There is an adaptation of this model in which l_max<l_max<previous, not included in this code
            ### This happens if a pathway can open between two fluid-containing sites with a pressure difference
            ### However, this rarely happened, didn't change the statistics, and took 10x the time to run. it has been removed
            if l_max>l_max_previous:
                tau_count=0
                tb_count=0
                all_broken=set()
                
                ### This line of code establishes all sites that will break following a global pressure increase.
                ### It's very slow. Could probably be sped up, but I'm not sure how. Tried many things and this was the fastest. It's also super unreadable.
                d_tobreak=dict({value: d_tau[value]-(d_s[value] - p_list[g_f.distance[value]]) for value in g_f.distance if d_tau[value]-(d_s[value] - p_list[g_f.distance[value]])>0.})
                while d_tobreak:
                    next_tobreak=max(d_tobreak.items(), key=operator.itemgetter(1))[0]
                    temp_broken=set()
                    ### Cycle through elements in next_tobreak, ensuring that they haven't already broken.
                    ### There is no longer a check below here to ensure site failure, so not having this check would cause sites to fail that don't meet the condition
                    if next_tobreak not in all_broken:
                        save_lmax.append(l_max)
                        save_linit.append(g_f.distance[next_tobreak])
                        tb_inside,tb_count,tau_count,all_inside,next_shell=0,0,0,True,{next_tobreak}
                        d_remaining={"temp":"temp"}
                        while d_remaining: 
                            remaining_sites=set(next_shell)
                            d_remaining={}
                            for k in remaining_sites:

                                ### If in g_f.distance, the site contains fluid. Wet fracture
                                if k in g_f.distance:
                                    if d_tau[k] >= d_s[k]-p_list[g_f.distance[k]]:                                             
                                        site_to_break=k
                                        diff=d_tau[site_to_break]
                                        d_remaining[k]=diff 
                                        tau_count+=diff
                                        d_tau[site_to_break]=0.
                                        broken_b.add(site_to_break)
                                        temp_broken.add(site_to_break)
                                        tb_count+=1
                                        tb_inside+=1
                                ### If not in g_f.distance, the site doesn't contain fluid. Dry fracture.
                                else:
                                    if d_tau[k] >= d_s[k]:
                                        site_to_break=k
                                        diff=d_tau[site_to_break]
                                        d_remaining[k]=diff
                                        tau_count+=diff
                                        d_tau[site_to_break]=0.
                                        broken_b.add(site_to_break)
                                        temp_broken.add(site_to_break)
                                        tb_count+=1
                            ### The propagation of this fracturing process has to go out in shells.
                            ### All neighbouring sites that fail will fail first, then all neighbours-of-neighbours, etc.
                            ### The failure conditions are checked shell-by-shell
                            ### Thankfully, because of a rectangular geometry and a point-source initiation, no two adjacent sites can fail at the same time
                            next_shell=set()                
                            for k in d_remaining:
                                ### Add new sites to the shell, and if a site doesn't yet exist in memory, sample tau and s values for it
                                diff=d_remaining[k]
                                x,y=k
                                adjacent_sites={(x+1,y),(x-1,y),(x,y+1),(x,y-1)}
                                if all_inside==True:
                                    for ww in adjacent_sites:
                                        if ww not in path:
                                            all_inside=False
                                next_shell=next_shell|adjacent_sites
                                for l in adjacent_sites:
                                    if l not in d_tau:
                                        d_tau[l]=random.random()
                                        d_s[l]=random.uniform(s_min,s_max)
                                    d_tau[l]=d_tau[l]+diff/4. #Add a quarter of diff from all adjacent sites

                        
                        ### This is just for saving stuff
                        after=len(temp_broken)
                        if after!=0:
                            rt_plot_mech.append(0)
                            rt_plot_t.append(i)
                            if all_inside==True:
                                in_out_markers.append(1)
                            else:
                            	in_out_markers.append(0)
                            area_size.append(after)
                            total_slips.append(tb_count)
                            energy_rel.append(tau_count)
                            event_counter+=1
                            temp_broken_list = list(temp_broken)  

                        ### Keep track of things that have broken to alleviate above problem
                        all_broken=all_broken|temp_broken
                    del d_tobreak[next_tobreak]


        ### Does fluid intiate a failure if lmax doesn't increase?
        else:
            tb_inside,tb_count,tau_count,all_inside,temp_broken=0,0,0,True,set()
            ### This section works almost the same as above, but the only site that could fail is the site recently invaded with fluid
            ### If it doesn't fail, this section is skipped.
            if d_tau[site_invade] >= d_s[site_invade] - p_list[g_f.distance[site_invade]]:
                save_lmax.append(l_max)
                save_linit.append(g_f.distance[next_tobreak])
                next_shell=set()
                next_shell.add(site_invade)
                d_remaining={"temp":"temp"}
                while d_remaining:      
                    remaining_sites=set(next_shell)
                    d_remaining={}
                    for k in remaining_sites:
                        if k in g_f.distance:
                            if d_tau[k] >= d_s[k]-p_list[g_f.distance[k]]:
                                site_to_break=k
                                diff=d_tau[site_to_break]
                                d_remaining[k]=diff
                                tau_count+=diff   
                                d_tau[site_to_break]=0.
                                broken_b.add(site_to_break)
                                temp_broken.add(site_to_break)
                                tb_count+=1
                                tb_inside+=1
                        else:
                            if d_tau[k] >= d_s[k]:    
                                site_to_break=k
                                diff=d_tau[site_to_break]
                                d_remaining[k]=diff
                                tau_count+=diff
                                d_tau[site_to_break]=0.
                                broken_b.add(site_to_break)
                                temp_broken.add(site_to_break)
                                tb_count+=1
                    next_shell=set()                        
                    for k in d_remaining:
                        diff=d_remaining[k]
                        x,y=k
                        adjacent_sites={(x+1,y),(x-1,y),(x,y+1),(x,y-1)}
                        if all_inside==True:
                            for ww in adjacent_sites:
                                if ww not in path:
                                    all_inside=False
                        next_shell=next_shell|adjacent_sites
                        for l in adjacent_sites:
                            if l not in d_tau: # Add new sites if needed
                                d_tau[l]=random.random()
                                d_s[l]=random.uniform(s_min,s_max)
                            d_tau[l]=d_tau[l]+diff/4. # Add a quarter of diff from all adjacent sites

                        
                        
                after=len(temp_broken)
                if after!=0:
                    area_size.append(after)
                    rt_plot_mech.append(1)
                    rt_plot_t.append(i)
                    event_counter+=1
                    if all_inside==True:
                        in_out_markers.append(1)
                    else:
                    	in_out_markers.append(0)
                    total_slips.append(tb_count)
                    energy_rel.append(tau_count)
                    temp_broken_list = list(temp_broken)

            

                        
### FLOW FLUID ###


        # Establish the biggest pressure difference
        # This looks incredibly inefficient, but is the fastest way I could find
        temp_values,temp_strength=[L_dict[j][0] for j in L_dict], [p_list[j]-L_dict[j][0] for j in L_dict]        
        max_where=fastest_argmax(temp_strength)
        max_val_strength,max_val=temp_strength[max_where], temp_values[max_where]


        # This is roughly 10x slower than above despite looking faster. Probably the slow for loops.
        # max_val_strength=-10000
        # for j in L_dict:
        #     if p_list[j]-L_dict[j][0]>max_val_strength:
        #         max_val_strength=p_list[j]-L_dict[j][0]
        #         max_val=L_dict[j][0]



        if True:
            ### Find the corresponding dictionary key in of site to be invaded through L_dict
            ### It also establishes the origin (source) of the bond breakage
            max_key,site_source=L_dict_backwards[max_val],d_f[L_dict[L_dict_backwards[max_val]][0]]


            ### Remove this item from the dictionaries. 
            ### It will now be filled with fluid, so we remove it from these checks to it speeds things up for later checks
            del d_f[max_val]
            del L_dict_backwards[max_val]

            if len(L_dict[max_key])==1:
                del L_dict[max_key]
            else:
                del L_dict[max_key][0]

            ### Remove the path correspondance in g_f
            for j in g_f.vertices[site_source]:
                if list(j.values())[0]==max_val:
                    site_invade=list(j.keys())[0]
                    g_f.remove_vertex(site_source,site_invade)
                    break

            ### If not already in the path, add it.
            ### This is a relic of the fluid-fluid breakage model, and should ALWAYS be true.
            ### Outputs an error if not.
            if site_invade not in path:
                path.add(site_invade)
                graph_f=bi_dict_add(graph_f,site_source,site_invade)
                (x,y),l_max_previous=site_invade,l_max
                g_f.update_distance(site_invade,max_key+1)

                ### Update l_max if needed
                if max_key+1 not in L_dict:
                    L_dict[max_key+1]=[]
                    if max_key+1>l_max:
                        l_max=max_key+1

                ### Sample tau and s values IF NEEDED
                if (x,y) not in d_tau and (x,y) not in broken_b:
                    d_tau[(x,y)],d_s[(x,y)]=random.random(),random.uniform(s_min,s_max)
                
                
                ### Find adjacent sites to newly invaded site, sample tau and s values for them.
                ### If needed, all of the directional dictionaries containing fluid connections are updated too
                directions=[(x+1,y),(x-1,y),(x,y+1),(x,y-1)]
                for j in directions:
                    if j not in g_f.distance:
                        r=random.random()
                        d_f[r]=(x,y)
                        g_f.add_vertex((x,y),{j:r}) 
                        bisect.insort_left(L_dict[max_key+1],r)
                        L_dict_backwards[r]=max_key+1

                    else:
                        if j not in graph_f[(x,y)]:
                            for k in g_f.vertices[j]:
                                (k_temp, val_temp),=k.items()
                                if k_temp==(x,y):
                                    r_temp=val_temp
                                    break
                            where_temp=L_dict_backwards[r_temp]
                            g_f.remove_vertex(j,(x,y))
                            del L_dict_backwards[r_temp]
                            L_dict[where_temp].remove(r_temp)
                            if len(L_dict[where_temp])==0:
                                del L_dict[where_temp]
                        
                
                if len(L_dict[max_key+1])==0:
                    del L_dict[max_key+1]
            else:
                print("ERROR") 

        ### Every 10000 steps, open the file, write data to it, then clear the lists to free up RAM
        ### This code is incredibly RAM heavy, so this is really important.
        if event_counter>thresh:
            with open(os.path.join('/scratch/clm','may_{k1}_{k2}_{k3}.csv'.format(k1=delta_p,k2=s_min,k3=s_max)),"a") as datafile:
                writer = csv.writer(datafile, delimiter='\t')
                writer.writerows(zip(in_out_markers, rt_plot_mech, total_slips, area_size, rt_plot_t, energy_rel,save_lmax,save_linit))
                in_out_markers, rt_plot_mech, total_slips, area_size, rt_plot_t, energy_rel, save_lmax,save_linit = [],[],[],[],[],[],[],[]
            datafile.close()
            thresh+=10000
    return in_out_markers, rt_plot_mech, total_slips, path, area_size, rt_plot_t


### Set your parameters!
iterations=100000
delta_p=0.3
s_min,s_max=1.3,2.3
tau_max=1.

t=time.time()
in_out_markers, rt_plot_mech, total_slips, path, area_size, rt_plot_t = breaks_loopless(iterations,delta_p,s_min,s_max,tau_max)
print(time.time()-t)