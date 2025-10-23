#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jan 12 17:36:29 2023

@author: fs
"""
class Counter:
  
  def __init__(self, n=0):
    self.n = n
  
  def increase(self):
    self.n += 1
    return self.n