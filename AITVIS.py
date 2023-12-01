#20231129-2 update _ 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
#-*- coding:utf-8 -*-
from array import array
from cgitb import text
from ctypes.wintypes import POINT
from distutils.cmd import Command
from itertools import filterfalse
from multiprocessing import Value
from re import I
from statistics import variance
from tkinter.tix import IMAGE, ROW
from turtle import bgcolor, width
from xml.dom.minidom import Identified
from PIL import Image,ImageDraw
from PIL import ImageTk
import tkinter as tk
import tkinter.ttk as ttk
import threading
import datetime
import cv2
import os
import numpy as np
import sys

import time
from datetime import datetime

from skimage.metrics import structural_similarity as compare_ssim
import imutils
import cv2
import argparse
from skimage.util import img_as_ubyte
#file
import pickle
import RPi.GPIO as GPIO
from os import path

import PIL.Image as pilimg

from sklearn import svm
from sklearn.model_selection import train_test_split
import shutil

import tensorflow as tf
from tensorflow.keras.applications import EfficientNetB0
from tensorflow.keras.preprocessing import image
from tensorflow.keras.applications.efficientnet import preprocess_input

from tkinter.filedialog import askdirectory
import tkinter.messagebox as messagebox
from scipy.signal import argrelextrema
import requests
import base64

pts_cnt = 1



pts_panel =[]
pts_panel2 =[]

btnCalc = []
pts_sx = []
pts_sy = []
pts_sw = []
pts_sh = []

pts_x = []
pts_y = []
pts_w = []
pts_h = []

pts_sx2 = []
pts_sy2 = []
pts_sw2 = []
pts_sh2 = []

pts_x2 = []
pts_y2 = []
pts_w2 = []
pts_h2 = []


pts_rrl = []
pts_rrh = []
pts_rgl = []
pts_rgh = []
pts_rbl = []
pts_rbh = []

pts2_rrl = []
pts2_rrh = []
pts2_rgl = []
pts2_rgh = []
pts2_rbl = []
pts2_rbh = []


btn_Pointset=[]
btn_Pointdis=[]
btn_Pointgap=[]
btn_Pointset2=[]
btn_Pointdis2=[]
btn_Pointgap2=[]

#capture check 
chk_capture =[]
chk_captureVar = []

chk_capture2 =[]
chk_captureVar2 = []

#filemove button
btn_filemovegood = []
btn_filemovebad = []
btn_filemoveinit = []

btn_filemovegood2 = []
btn_filemovebad2 = []
btn_filemoveinit2 = []

rois =[]
rois2 =[]

pointcount = 7
pointcount2 = 7
w_max = 640
h_max = 360
points_std = []
points_std2 = []

points_roi_std = []
points_roi_std2 = []

#OK,NG결과 이미지
label_list_result = []
label_list_result_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
label_list_result_OK_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
label_list_result_NG_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
label_list_result2 = []
label_list_result2_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
label_list_result2_OK_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
label_list_result2_NG_cnt = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
pt1_v1 = 115
popup_cnt=0

resultPt = []
resultPt2 = []
isresult = False
isComplete = False
roi1 = []
#???? ??
bgrroi= []
roiMean=[]

bgrroi2= []
roiMean2=[]

lb_result = []
rb_vals= []

Ck_inspType_Var1=[]
Ck_inspType_Var2=[]

Ck2_inspType_Var1=[]
Ck2_inspType_Var2=[]
cnt = 0
cnt2 = 0

cam2Finish_chk=False
cam1Finish_chk=False

isng_event = threading.Event()
isng=False
cam1Wait = False

cam1_result_gpio = 5
cam2_result_gpio = 4
input_gpio = 22
modelChange_gpio = 4

GPIO.setmode(GPIO.BCM)
GPIO.setup(input_gpio,GPIO.IN,pull_up_down =GPIO.PUD_DOWN)
GPIO.setup(modelChange_gpio,GPIO.IN,pull_up_down =GPIO.PUD_DOWN)

GPIO.setup(14,GPIO.OUT) #cam1 result
GPIO.setup(15,GPIO.OUT) #cam2 result
GPIO.setup(cam1_result_gpio,GPIO.OUT)
GPIO.setup(cam2_result_gpio,GPIO.OUT)

modelchange_chk= 0
exGPIO17 = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
exGPIO17_time = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
exGPIO17_state=0
resultratio1 = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
resultratio2 = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]

isFinish=False
GPIO.output(5,True)
GPIO.output(14,True)
GPIO.output(15,True)


popup_created = False   
result_popup = None

#auth & popup
popup_list = []

popup_created = False
passwd = 1111
authConfirm = False

#result view

result_view_image1 = []
result_view_image2 = []

def cam2Thread():
   
    global bgrroi2
    global cam2Finish_chk
    global cnt2
    global isFinish
    global isng,isng_event,cam1Wait
    global result_view_image2
    global label_list_result,label_list_result2
    global authConfirm
    global modelchange_chk,exGPIO17_state,exGPIO17,exGPIO17_time

    isng2 = False
    panel2 = None
    panel2_cap2 = None
    
    panel_result2 = None
    image_size2 = (50, 50)
    
    # 클래스 레이블 정의
    CAM2_class_names = ['good', 'bad']

    # EfficientNetB0 모델 불러오기 (전체 레이어 동결)
    CAM2_1_base_model = EfficientNetB0(weights='imagenet', include_top=False, input_shape=(100, 100, 3))
    CAM2_1_base_model.trainable = False

    # 모델 구성
    CAM2_1_1_model = tf.keras.Sequential([
        CAM2_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM2_1_2_model = tf.keras.Sequential([
        CAM2_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM2_2_1_model = tf.keras.Sequential([
        CAM2_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM2_2_2_model = tf.keras.Sequential([
        CAM2_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])

    # 학습된 모델 가중치 불러오기
    CAM2_1_1_model.load_weights('DAMPER_2_1_1.h5')
    CAM2_1_2_model.load_weights('DAMPER_2_1_2.h5')
    CAM2_2_1_model.load_weights('DAMPER_2_2_1.h5')
    CAM2_2_2_model.load_weights('DAMPER_2_2_2.h5')

    
    ptsrois2 = []

    color = []
    cap = cv2.VideoCapture(2)
    cap.set(cv2.CAP_PROP_FRAME_WIDTH,w_max)
    cap.set(cv2.CAP_PROP_FRAME_HEIGHT,h_max)
    cap.set(cv2.CAP_PROP_FOURCC,cv2.VideoWriter_fourcc('M','J','P','G'))
   

    dt2 = time.time() * 1000
    dt2_chk = time.time() * 1000
    
    print("----------camera setting--------")
    for i in range(1,pointcount2+1):
        pts_sh2[i-1].set(pts_h2[i-1])
        pts_sw2[i-1].set(pts_w2[i-1])
        #pts_h[i-1] = 10
        #pts_w[i-1] = 10
        pts_sx2[i-1].set(pts_x2[i-1])
        pts_sy2[i-1].set(pts_y2[i-1])
        
        label_list_result2.append(0)
    print("----------camera start----------")



    if (cap.isOpened() == False):
        cap.release()
        cv2.destroyAllWindows()
        print("Unable")
       
    while True:
        ret,color = cap.read()
        if not ret:
            print("cam2 error")
            cap.release()
            cv2.destroyAllWindows()
            os.system('sudo reboot')
            continue
            
        if ret:

            # 특정 색상 범위 내의 색상만 변경
            

            image2 = cv2.cvtColor(color,cv2.COLOR_BGR2RGB)
            lower_red = np.array([0, 0, 200])
            upper_red = np.array([50, 50, 255])

            # 이미지에서 빨간색 범위 내의 픽셀 찾기
            red_mask = cv2.inRange(image2, lower_red, upper_red)

            # 빨간색 범위 내의 픽셀을 특정 색상(예: 흰색)으로 변경
            image2[red_mask != 0] = [255, 255, 255]
            

            x=320; y=150; w=10; h=10
            result_image2 = []
            
            if ((GPIO.input(modelChange_gpio)==0)):
                modelchange_chk=0 #model 2
            else:
                modelchange_chk=1 #model 1
                

            #if ((GPIO.input(input_gpio)==0) and exGPIO17_state==1):
            #    print("CAM2____INIT")
            #    exGPIO17 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
            #    exGPIO17_state=0
            if ((GPIO.input(input_gpio)==1) and isFinish == False):
                print("CAM2____START")
                dtstart = time.time()*1000
                exGPIO17_state=1
                exGPIO17_time.append(dtstart)
                exGPIO17_time.pop(0)
                print(dtstart-exGPIO17_time[24])
                print(dtstart-exGPIO17_time[23])
                print(dtstart-exGPIO17_time[22])
                print(dtstart-exGPIO17_time[21])
                print(dtstart-exGPIO17_time[20])
                print(dtstart-exGPIO17_time[19])
                if dtstart-exGPIO17_time[24] <1000:
                    exGPIO17[24]=1
                else:
                    exGPIO17[24]=0
                if dtstart-exGPIO17_time[23] <1000:
                    exGPIO17[23]=1
                else:
                    exGPIO17[23]=0
                if dtstart-exGPIO17_time[22] <1000:
                    exGPIO17[22]=1
                else:
                    exGPIO17[22]=0
                if dtstart-exGPIO17_time[21] <1000:
                    exGPIO17[21]=1
                else:
                    exGPIO17[21]=0
                if dtstart-exGPIO17_time[20] <1000:
                    exGPIO17[20]=1
                else:
                    exGPIO17[20]=0
                if dtstart-exGPIO17_time[19] <1000:
                    exGPIO17[19]=1
                else:
                    exGPIO17[19]=0
                    
                
                #exGPIO17.append(1)
                #exGPIO17.pop(0)
                print(len(exGPIO17))
                
                #rightMng()
            if np.sum(exGPIO17) ==6 and isFinish == False:
                isFinish = True
                dt2 = time.time() * 1000
                print('----cam2----')
                print(exGPIO17)

            if np.sum(exGPIO17) > 6 and isFinish == False:
                exGPIO17_state==0
                exGPIO17_time = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                exGPIO17 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                
            isng2 = False
            if (time.time() * 1000 - dt2 > 500 and isFinish == True):
                
                print("--------ing2------")
                #exGPIO17 = GPIO.input(17)
                exGPIO17_time = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                exGPIO17 = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                print("-----------")
                cnt2 = cnt2 + 1
                print(cnt2)
                cam2Finish_chk = True
                
                #print(exGPIO17)
                isFinish = False
                #GPIO.output(5,True)
                #print(cam2Finish_chk)
                #cam2Finish_chk = False
                result_image2 = image2
                result_image2 = cv2.resize(result_image2, (w_max, h_max+120))
                result_view_image2 = result_image2
                
                
                for i in range(1,pointcount2+1):
                    roi2 = np.zeros(result_image2.shape[:2], np.uint8)
                    roi2 = cv2.circle(roi2, (int(pts_x2[i-1]), int(pts_y2[i-1])), int(pts_w2[i-1]), 255, cv2.FILLED)
                    # BGR로 색 추출
                    #bgrLower = np.array([pts2_rrl[i-1], pts2_rgl[i-1], pts2_rbl[i-1]])    # 추출할 색의 하한(BGR)
                    #bgrUpper = np.array([pts2_rrh[i-1], pts2_rgh[i-1], pts2_rbh[i-1]])    # 추출할 색의 상한(BGR)

                    print(f"{pts2_rrl[i-1]}-{pts2_rrh[i-1]},{pts2_rgl[i-1]}-{pts2_rgh[i-1]},{pts2_rbl[i-1]}-{pts2_rbh[i-1]}")
                    
                    mask2 = np.ones_like(result_image2) * 255
                    mask2 = cv2.bitwise_and(mask2, result_image2, mask=roi2) + cv2.bitwise_and(mask2, mask2, mask=~roi2)

                    
                    
                    cv2.imwrite(os.getcwd()+f'/result/test/CAM2_{i}.PNG',mask2)
                    # 자를 영역 지정 (좌상단과 우하단 좌표)
                    x1, y1 = int(pts_x2[i-1])-50, int(pts_y2[i-1])-50  # 좌상단 좌표
                    x2, y2 = int(pts_x2[i-1])+50, int(pts_y2[i-1])+50  # 우하단 좌표


                    
                    if int(pts_x2[i-1])-50 < 0:
                        x1 = 0

                    if int(pts_y2[i-1])-50 < 0:
                        y1 = 0

                    if int(pts_x2[i-1])+50 < 100:
                        x2 = 100

                    if int(pts_y2[i-1])+50 < 100:
                        y2 = 100
                                        # 이미지 자르기
                    cropped_image = mask2[y1:y2, x1:x2]
                    print(cropped_image.shape)

                    cv2.imwrite(os.getcwd()+f'/result/test/CAM2_result_{i}.PNG',cropped_image)

                    if chk_captureVar2[i-1].get() == 1:
                        if not os.path.exists(os.getcwd() + '/result/liveImg/' + str(datetime.now().strftime("%Y%m%d"))):
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d")))
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/3')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/4')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/5')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/6')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/7')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/8')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/9')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/10')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/11')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/12')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/13')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/14')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/15')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/16')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/3')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/4')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/5')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/6')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/7')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/8')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/9')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/10')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/11')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/12')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/13')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/14')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/15')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/16')
                            #("1")
                            cv2.imwrite(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG', cropped_image)
                            print(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG')
                        else:
                            #print("2")
                            cv2.imwrite(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG', cropped_image)
                            print(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG')

                    
                    
                    if i==1:
                        #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_result222_{i}.PNG',cropped_image)
                        x = cv2.cvtColor(cropped_image,cv2.COLOR_BGR2RGB)
                        x = x.astype('float32')
                        x = preprocess_input(x)
                        x = np.expand_dims(x, axis=0)
                        
                        preds = ""
                        if modelchange_chk == 1:
                            print("model 1")
                            preds = CAM2_1_1_model.predict(x)
                        else:
                            print("model 2")
                            preds = CAM2_1_2_model.predict(x)

                        print(int(preds[0][1]*100))
                        resultratio2[i-1]=int(preds[0][1]*100)
                        #("Accuracy:", accuracy)
                        outfile =os.getcwd()+'/result/test/CAM2_1_'+ str(datetime.now().strftime("%Y%m%d"))+'.txt'
                        with open(outfile,'a') as file:
                            if(preds[0][1]*100<int(pts_h2[i-1])):
                                print(str(i)+"_CAM2_bad.")
                                label_list_result2[i-1]=0
                                #file.write(f'bad,{preds[0][1]}_cam2\n')
                            else:
                                print(str(i)+"_CAM2_good")
                                label_list_result2[i-1]=1
                                #file.write(f'good,{preds[0][1]}_cam2\n')
                    elif i==2:
                        #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_result222_{i}.PNG',cropped_image)
                        x = cv2.cvtColor(cropped_image,cv2.COLOR_BGR2RGB)
                        x = x.astype('float32')
                        x = preprocess_input(x)
                        x = np.expand_dims(x, axis=0)

                        preds = ""
                        if modelchange_chk == 1:
                            print("model 1")
                            preds = CAM2_2_1_model.predict(x)
                        else:
                            print("model 2")
                            preds = CAM2_2_2_model.predict(x)

                        print(int(preds[0][1]*100))
                        resultratio2[i-1]=int(preds[0][1]*100)
                        print(f"result2 {resultratio2[i-1]}")
                        #("Accuracy:", accuracy)
                        outfile =os.getcwd()+'/result/test/CAM2_2_'+ str(datetime.now().strftime("%Y%m%d"))+'.txt'
                        with open(outfile,'a') as file:
                            if(preds[0][1]*100<int(pts_h2[i-1])):
                                print(str(i)+"_CAM2_bad.")
                                label_list_result2[i-1]=0
                                #file.write(f'bad,{preds[0][1]}_cam2\n')
                            else:
                                print(str(i)+"_CAM2_good")
                                label_list_result2[i-1]=1
                                #file.write(f'good,{preds[0][1]}_cam2\n')
                                
                    else:
                        print("pass")
                       
                print(f"sum(label_list_result2):{sum(label_list_result2)} , pointcount2 : {pointcount2}")
                if sum(label_list_result2) != pointcount2:
                    #isng2 = False #bypass always ok
                    isng2 = True  #live
                    #GPIO.output(15,False)
                    #GPIO.output(15,True)
                    #print("bad.")
                    #cnt2=0
                else:
                    isng2 = False
                    #GPIO.output(15,False)
                    #print("good")
                    #cnt2=0

                result_image2 = mask2



                result_image2 = image2
                result_image2 = cv2.resize(result_image2, (w_max, h_max))
                
                result_image2 = Image.fromarray(result_image2)
                result_image2 = ImageTk.PhotoImage(result_image2)
               

                if panel2_cap2 is None:
                    panel2_cap2 = tk.Label(image=result_image2)
                    panel2_cap2.image = image2
                    Tab_Image.add(panel2_cap2, text="CAP2")
                   
                else:
                    panel2_cap2.configure(image=result_image2)
                    panel2_cap2.image=result_image2


            if(time.time() * 1000 - dt2_chk > 500 and cam2Finish_chk == True):
                dt2_chk = time.time() * 1000
                print("fdfads")
                cam2Finish_chk = False
                
                cam1Wait = True
                isng_event.wait()
                print(f"Cam1__{isng}")
                print(f"Cam2__{isng2}")
                isFinish=False
                print(isFinish)
                
                if isng ==False and isng2 == False:
                    print("1")
                    GPIO.output(cam1_result_gpio,False)
                    GPIO.output(cam2_result_gpio,False)
                    print("----end----")
                    time.sleep(1)
                    GPIO.output(cam1_result_gpio,True)
                    GPIO.output(cam2_result_gpio,True)

                
                isng = False
                
                print(result_view_image2)
                show_popup(1)
                label_list_result = np.zeros_like(label_list_result)
                label_list_result2 = np.zeros_like(label_list_result2)
                #("CAM2")
                #print(isng2)
                curdate = time.strftime('%Y%m%d')
                f = open("result/CAM2_"+curdate+".txt","a")
                f.write(str(isng2) + " ")
                f.write(str(datetime.now())+ "\n")
                f.close()
                if isng2 == True:
                    #GPIO.output(15,True)
                    NGimg2=Image.open(os.getcwd()+'/img/NG.JPG')
                    NGimg2= NGimg2.resize((30, 30), Image.LANCZOS)
                    result_NG2 = ImageTk.PhotoImage(NGimg2)

                else:
                    #GPIO.output(15,False)
                    OKimg2=Image.open(os.getcwd()+'/img/OK.JPG')
                    OKimg2= OKimg2.resize((30, 30), Image.LANCZOS)
                    result_OK2 = ImageTk.PhotoImage(OKimg2)

			

            #-----------------inspection region

            #1. ROI ????Ʈ ?׸???
            for i in range(1,pointcount2+1):
                image2 = cv2.circle(image2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),1)

                cv2.putText(image2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+30-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                cv2.putText(image2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])-10,int(pts_y2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                resultPt2[i-1]=1

              


            image2 = Image.fromarray(image2)
            image2 = ImageTk.PhotoImage(image2)

           
            if panel2 is None:
                panel2 = tk.Label(image=image2)
                panel2.image = image2
                Tab_Image.add(panel2, text="CAM2")
            else:
                panel2.configure(image=image2)
                panel2.image=image2
    cap.release()            
        

def camThread():

    global roi1
    global bgrroi

    global pointcount

    global isComplete
    global isresult
    global resultPt
   
    global cam1
    
    
    global cam1Finish_chk
    global cnt2
    global cnt
    
    global isng,isng_event,cam1Wait
    global result_view_image1
    global authConfirm
    global modelchange_chk
    
    
    isng = False
    

    

    image_size = (50, 50)
    

        # 클래스 레이블 정의
    CAM1_class_names = ['good', 'bad']

    # EfficientNetB0 모델 불러오기 (전체 레이어 동결)
    CAM1_1_base_model = EfficientNetB0(weights='imagenet', include_top=False, input_shape=(100, 100, 3))
    CAM1_1_base_model.trainable = False

    # 모델 구성
    CAM1_1_1_model = tf.keras.Sequential([
        CAM1_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM1_1_2_model = tf.keras.Sequential([
        CAM1_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM1_2_1_model = tf.keras.Sequential([
        CAM1_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    CAM1_2_2_model = tf.keras.Sequential([
        CAM1_1_base_model,
        tf.keras.layers.Conv2D(128, (3, 3), activation='relu'), #64개의 필터를 사용한다. 그 필터는 3,3크기이다.
        tf.keras.layers.GlobalAveragePooling2D(),
        tf.keras.layers.Dropout(0.5),
        tf.keras.layers.BatchNormalization(),
        tf.keras.layers.Dense(2, activation='softmax')
    ])
    # 학습된 모델 가중치 불러오기
    CAM1_1_1_model.load_weights('DAMPER_1_1_1.h5')
    CAM1_1_2_model.load_weights('DAMPER_1_1_2.h5')
    CAM1_2_1_model.load_weights('DAMPER_1_2_1.h5')
    CAM1_2_2_model.load_weights('DAMPER_1_2_2.h5')

    
    color = []
    cap = cv2.VideoCapture(0)
    cap.set(cv2.CAP_PROP_AUTOFOCUS,0) #????? ??????????????? ?????? ??????
    cap.set(cv2.CAP_PROP_FRAME_WIDTH,w_max)
    cap.set(cv2.CAP_PROP_FRAME_HEIGHT,h_max)
    cap.set(cv2.CAP_PROP_FOURCC,cv2.VideoWriter_fourcc('M','J','P','G'))
    

    
    imagecnt = 0
    img_list = []
    
    cap.set(28,40)
    apts = np.load('./pts.npy')
    #print(apts)
    panel = None
    panel_bit = None
    #????? ???? ???г?
    panel_result = None

    ptsrois = []
   
    #thread?? ???????? ????
    dt = time.time() * 1000
    dt_finish = time.time() * 1000

    print("----------camera setting--------")
   
    for i in range(1,pointcount+1):
        pts_sh[i-1].set(pts_h[i-1])
        pts_sw[i-1].set(pts_w[i-1])
        #pts_h[i-1] = 10
        #pts_w[i-1] = 10
        pts_sx[i-1].set(pts_x[i-1])
        pts_sy[i-1].set(pts_y[i-1])

        label_list_result.append(0)

    if authConfirm:
        for i in range(1,pointcount+1):
            pts_sh[i-1].config(state="normal")
            pts_sw[i-1].config(state="normal")
            pts_sx[i-1].config(state="normal")
            pts_sy[i-1].config(state="normal")
    else:
        for i in range(1,pointcount+1):
            pts_sh[i-1].config(state="disabled")
            pts_sw[i-1].config(state="disabled")
            pts_sx[i-1].config(state="disabled")
            pts_sy[i-1].config(state="disabled")
        
       
   

    print("----------camera start----------")



    if (cap.isOpened() == False):
        cap.release()
        cv2.destroyAllWindows()
        print("Unable")
       
    while True:
        ret,color = cap.read()
        if not ret:
            print("cam1 error")
            cap.release()
            cv2.destroyAllWindows()
            os.system('sudo reboot')
            continue
        
        if ret:
           
            image = cv2.cvtColor(color,cv2.COLOR_BGR2RGB)
           
            grayImage = cv2.cvtColor(image , cv2.COLOR_BGR2GRAY)

           
            ret, dst = cv2.threshold(grayImage, 150, 255, cv2.THRESH_BINARY)
            hsvImage = cv2.cvtColor(image , cv2.COLOR_BGR2HSV)

            laplacian = cv2.Laplacian(grayImage, cv2.CV_8U, ksize=5)


            lower_blue = np.array([110, 100, 100])
            upper_blue = np.array([130, 255, 255])

            lower_green = np.array([50, 100, 100])
            upper_green = np.array([70, 255, 255])

            lower_red = np.array([-10, 100, 100])
            upper_red = np.array([10, 255, 255])


           
            x=320; y=150; w=10; h=10        #
            
            result_image = []
            
            
            while cam1Wait:
                print("cam1Wait---start")
                if sum(label_list_result) != pointcount:
                    print("CAM1----------bad")
                    isng_event.set()
                    isng=True
                    cam1Wait = False
                    isng_event.clear()
                else:
                    print("CAM1----------good")
                    isng_event.set()
                    isng=False
                    cam1Wait = False
                    isng_event.clear()
            
            #isng = False
            
            if(time.time() * 1000 - dt > 800 and isFinish == True):
                dt = time.time() * 1000
                cam1Finish_chk = True
                
                result_image = image
                result_image = cv2.resize(result_image, (w_max, h_max+120))
                result_view_image1 = result_image
                
                for i in range(1,pointcount+1):
                    roi = np.zeros(result_image.shape[:2], np.uint8)
                    roi = cv2.circle(roi, (int(pts_x[i-1]), int(pts_y[i-1])), int(pts_w[i-1]), 255, cv2.FILLED)

                    mask = np.ones_like(result_image) * 255
                    mask = cv2.bitwise_and(mask, result_image, mask=roi) + cv2.bitwise_and(mask, mask, mask=~roi)
                    #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_{i}.PNG',mask)

                   
                    # 자를 영역 지정 (좌상단과 우하단 좌표)
                    x1, y1 = int(pts_x[i-1])-50, int(pts_y[i-1])-50  # 좌상단 좌표
                    x2, y2 = int(pts_x[i-1])+50, int(pts_y[i-1])+50  # 우하단 좌표
                    
                    if int(pts_x[i-1])-50 < 0:
                        x1 = 0

                    if int(pts_y[i-1])-50 < 0:
                        y1 = 0

                    if int(pts_x[i-1])+50 < 100:
                        x2 = 100

                    if int(pts_y[i-1])+50 < 100:
                        y2 = 100

                    # 이미지 자르기
                    cropped_image = mask[y1:y2, x1:x2]
                    print(cropped_image.shape)


                    #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_result_{i}.PNG',cropped_image)


                    if chk_captureVar[i-1].get() == 1:
                        if not os.path.exists(os.getcwd() + '/result/liveImg/' + str(datetime.now().strftime("%Y%m%d"))):
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d")))
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/3')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/4')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/5')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/6')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/7')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/8')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/9')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/10')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/11')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/12')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/13')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/14')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/15')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM1/16')
                            
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/1')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/2')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/3')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/4')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/5')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/6')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/7')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/8')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/9')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/10')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/11')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/12')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/13')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/14')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/15')
                            os.makedirs(os.getcwd() + '/result/liveImg/' +str(datetime.now().strftime("%Y%m%d"))+'/CAM2/16')
                            cv2.imwrite(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM1/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG', cropped_image)
                        else:
                            cv2.imwrite(os.getcwd()+'/result/liveImg/'+ str(datetime.now().strftime("%Y%m%d"))+'/CAM1/'+str(i)+'/'+str(datetime.now().strftime("%Y%m%d%H%M%S"))+'.PNG', cropped_image)

                    
                    
                    if i==1:
                        #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_result222_{i}.PNG',cropped_image)
                        x = cv2.cvtColor(cropped_image,cv2.COLOR_BGR2RGB)
                        x = x.astype('float32')
                        x = preprocess_input(x)
                        x = np.expand_dims(x, axis=0)

                        preds = ""
                        if modelchange_chk == 1:
                            print("cam1 model 1")
                            preds = CAM1_1_1_model.predict(x)
                        else:
                            print("cam1 model 2")
                            preds = CAM1_1_2_model.predict(x)

                        print(int(preds[0][1]*100))
                        resultratio1[i-1]=int(preds[0][1]*100)
                        #("Accuracy:", accuracy)
                        outfile =os.getcwd()+'/result/test/CAM1_1_'+ str(datetime.now().strftime("%Y%m%d"))+'.txt'
                        with open(outfile,'a') as file:
                            if(preds[0][1]*100<int(pts_h[i-1])):
                                print(str(i)+"_CAM1_bad.")
                                label_list_result[i-1]=0
                                #file.write(f'bad,{preds[0][1]}_cam1\n')
                            else:
                                print(str(i)+"_CAM1_good")
                                label_list_result[i-1]=1
                                #file.write(f'good,{preds[0][1]}_cam1\n')
                    elif i==2:
                        #cv2.imwrite(os.getcwd()+f'/result/test/CAM1_result222_{i}.PNG',cropped_image)
                        x = cv2.cvtColor(cropped_image,cv2.COLOR_BGR2RGB)
                        x = x.astype('float32')
                        x = preprocess_input(x)
                        x = np.expand_dims(x, axis=0)

                        preds = ""
                        if modelchange_chk == 1:
                            print("cam1 model 1")
                            preds = CAM1_2_1_model.predict(x)
                        else:
                            print("cam1 model 2")
                            preds = CAM1_2_2_model.predict(x)

                        print(int(preds[0][1]*100))
                        resultratio1[i-1]=int(preds[0][1]*100)
                        #("Accuracy:", accuracy)
                        outfile =os.getcwd()+'/result/test/CAM1_2_'+ str(datetime.now().strftime("%Y%m%d"))+'.txt'
                        with open(outfile,'a') as file:
                            if(preds[0][1]*100<int(pts_h[i-1])):
                                print(str(i)+"_CAM1_bad.")
                                label_list_result[i-1]=0
                                #file.write(f'bad,{preds[0][1]}_cam1\n')
                            else:
                                print(str(i)+"_CAM1_good")
                                label_list_result[i-1]=1
                                #file.write(f'good,{preds[0][1]}_cam1\n')
                    else:
                        print("pass")

                    print(f"sum(label_list_result):{sum(label_list_result)} , pointcount : {pointcount}")
                    if sum(label_list_result) != pointcount:
                        isng = True  #live
                    else:
                        isng = False
					
                    
                result_image = mask
           
            if(time.time() * 1000 - dt_finish > 1000 and cam1Finish_chk == True):
                dt_finish = time.time() * 1000
                cam1Finish_chk = False
                #?????? ????
                #print("CAM1")
                #print(isng)
                curdate = time.strftime('%Y%m%d')
                f = open("result/CAM1_"+curdate+".txt","a")
                f.write(str(isng) + " ")
                f.write(str(datetime.now())+ "\n")
                f.close()
                
                
                if isng == True:
                    #GPIO.output(14,True)
                    NGimg=Image.open(os.getcwd()+'/img/NG.JPG')
                    NGimg= NGimg.resize((30, 30), Image.LANCZOS)
                    result_NG = ImageTk.PhotoImage(NGimg)
                    
                else:
                    #GPIO.output(14,False)
                    OKimg=Image.open(os.getcwd()+'/img/OK.JPG')
                    OKimg= OKimg.resize((30, 30), Image.LANCZOS)
                    result_OK = ImageTk.PhotoImage(OKimg)

            for i in range(1,pointcount+1):
                image = cv2.circle(image,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),1)
                cv2.putText(image, f'{i}', (int(pts_x[i-1])+int(pts_w[i-1]),int(pts_y[i-1])+30-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                cv2.putText(image, f'{resultratio1[i-1]}', (int(pts_x[i-1])-10,int(pts_y[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                resultPt[i-1]=1



            image = Image.fromarray(image)
            image = ImageTk.PhotoImage(image)

           
            if panel is None:
                panel = tk.Label(image=image)
                panel.image = image
                panel.grid(column=0, row=0,rowspan=3)
                Tab_Image.add(panel, text="CAM1")
            else:
                panel.configure(image=image)
                panel.image=image


        dt_chk = time.time() * 1000
        
        if dt_chk - dt > 500 and cam1Finish_chk == True:
            dt_chk = time.time() * 1000
            cam1Finish_chk == False
            
            OKimg=Image.open(os.getcwd()+'/img/OK.JPG')
            OKimg= OKimg.resize((30, 30), Image.LANCZOS)
            result_OK = ImageTk.PhotoImage(OKimg)
            #if isng == True:
            #    print("NG2")
            #else: 
            #    print("OK2")
            if panel_result is None:
                panel_result = tk.Label(image=result_OK)
                panel_result.image = result_OK
                Tab_set2.grid(column=1, row=0, padx=0, pady=0)
                Tab_set2.add(panel_result, text="RESULT1")
            else:
                panel_result.configure(image=result_OK)
                panel_result.image=result_OK
    cap.release()



def show_popup(value):
    global result_popup,popup_created, ok_img, ng_img
    global result_view_image1,result_view_image2
    global w_max, h_max,popup_cnt
    lb_Result_img=[]
    lb_Result_img2=[]
    
    print(f"popup_created {popup_created} ")
    def close_popup():
        global popup_cnt
        print(f"popup_close_{popup_cnt}")
        print("close")
        popup_cnt=0
        global popup_created
        popup_created = False
        result_popup.destroy()
        
            

    popup_created
    if not popup_created:
        popup_created = True
        result_popup = tk.Toplevel()
        result_popup.title("result")
        result_popup.geometry("+{}+{}".format(root.winfo_rootx() -200, root.winfo_rooty() + 1))
        result_popup.protocol("WM_DELETE_WINDOW",close_popup)


    pop_cam1_result = tk.LabelFrame(result_popup, text="CAM1_RESULT")
    pop_cam1_result.grid(column=1, row=1, padx=0, pady=0)
    pop_cam2_result = tk.LabelFrame(result_popup, text="CAM2_RESULT")
    pop_cam2_result.grid(column=2, row=1, padx=0, pady=0)

    Okimg = Image.open(os.getcwd() + '/img/OK.JPG')
    Okimg = Okimg.resize((33, 33), Image.LANCZOS)
    ok_img = ImageTk.PhotoImage(Okimg)

    NGimg = Image.open(os.getcwd() + '/img/NG.JPG')
    NGimg = NGimg.resize((33, 33), Image.LANCZOS)
    ng_img = ImageTk.PhotoImage(NGimg)

    if result_view_image2 != [] and result_view_image1 != []:


        #for i in range(1,pointcount+1):
        #    result_view_image1 = cv2.circle(result_view_image1,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),1)
        #    cv2.putText(result_view_image1, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)

        image1 = []
        image1 = Image.fromarray(result_view_image1)
        image_cv1_cropped = image1.crop((0, 0, min(450, image1.width), min(400, image1.height)))
        photo_image1 = ImageTk.PhotoImage(image_cv1_cropped)
        image2 = []
        image2 = Image.fromarray(result_view_image2)
        image_cv2_cropped = image2.crop((0, 0, min(450, image2.width), min(400, image2.height)))
        photo_image2 = ImageTk.PhotoImage(image_cv2_cropped)

        image_cv1 = np.array(image_cv1_cropped)
        image_cv1 = cv2.cvtColor(image_cv1, cv2.COLOR_RGB2BGR)

        image_cv2 = np.array(image_cv2_cropped)
        image_cv2 = cv2.cvtColor(image_cv2, cv2.COLOR_RGB2BGR)
        #label_list_result = [1,0,1,1,1,0,0,1,1,1]
        popup_cnt=popup_cnt+1
        for i in range(1,pointcount+1):
            if i == 1:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    label_list_result_OK_cnt[i-1]=label_list_result_OK_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result_NG_cnt[i-1]=label_list_result_NG_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 2:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    label_list_result_OK_cnt[i-1]=label_list_result_OK_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result_NG_cnt[i-1]=label_list_result_NG_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 3:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    label_list_result_OK_cnt[i-1]=label_list_result_OK_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result_NG_cnt[i-1]=label_list_result_NG_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 4:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    label_list_result_OK_cnt[i-1]=label_list_result_OK_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result_NG_cnt[i-1]=label_list_result_NG_cnt[i-1]+1
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 5:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 6:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 7:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 8:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 9:
                label_list_result_cnt[i-1] = label_list_result_cnt[i-1] +1
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 10:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 11:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 12:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 13:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 14:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 15:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 16:
                if label_list_result[i-1] == 1:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,255,0),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv1 = cv2.circle(image_cv1,(int(pts_x[i-1]),int(pts_y[i-1])),int(pts_w[i-1]),(0,0,255),2)
                    cv2.putText(image_cv1, f'{i}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv1, f'{resultratio1[i-1]}', (int(pts_x[i-1]-100)+int(pts_w[i-1]),int(pts_y[i-1])+int(pts_h[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)

        for i in range(1,pointcount2+1):
            if i == 1:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    label_list_result2_OK_cnt[i-1]=label_list_result2_OK_cnt[i-1]+1
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result2_NG_cnt[i-1]=label_list_result2_NG_cnt[i-1]+1
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 2:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    label_list_result2_OK_cnt[i-1]=label_list_result2_OK_cnt[i-1]+1
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    label_list_result2_NG_cnt[i-1]=label_list_result2_NG_cnt[i-1]+1
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 3:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 4:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 5:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 6:
                label_list_result2_cnt[i-1] = label_list_result2_cnt[i-1] +1
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 7:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 8:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 9:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 10:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 11:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 12:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 13:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 14:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 15:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
            elif i == 16:
                if label_list_result2[i-1] == 1:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                else:
                    image_cv2 = cv2.circle(image_cv2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,0,255),2)
                    cv2.putText(image_cv2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
                    cv2.putText(image_cv2, f'{resultratio2[i-1]}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-60) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)

        text_position1 = (10,80)
        text_color_OK_1 = (0,255,0)
        text_color_NG_1 = (0,0,255)
        text_font1 = cv2.FONT_HERSHEY_SIMPLEX
        text_scale1 = 3.0
        text_thickness1 = 5
        if pointcount == sum(label_list_result):
            cv2.putText(image_cv1,"OK",text_position1,text_font1,text_scale1,text_color_OK_1,text_thickness1)
        else:
            cv2.putText(image_cv1,"NG",text_position1,text_font1,text_scale1,text_color_NG_1,text_thickness1)


        text_position2 = (10,80)
        text_color_OK_2 = (0,255,0)
        text_color_NG_2 = (0,0,255)
        text_font2 = cv2.FONT_HERSHEY_SIMPLEX
        text_scale2 = 3.0
        text_thickness2 = 5
        if pointcount2 == sum(label_list_result2):
            cv2.putText(image_cv2,"OK",text_position2,text_font2,text_scale2,text_color_OK_2,text_thickness2)
        else:
            cv2.putText(image_cv2,"NG",text_position2,text_font2,text_scale2,text_color_NG_2,text_thickness2)
            
        resized_image1 = cv2.resize(image_cv1,(350,300),interpolation=cv2.INTER_AREA)
        image_with_circle = Image.fromarray(cv2.cvtColor(resized_image1, cv2.COLOR_BGR2RGB))
        photo_image1 = ImageTk.PhotoImage(image_with_circle)


        resized_image2 = cv2.resize(image_cv2,(350,300),interpolation=cv2.INTER_AREA)
        image_with_circle2 = Image.fromarray(cv2.cvtColor(resized_image2, cv2.COLOR_BGR2RGB))
        photo_image2 = ImageTk.PhotoImage(image_with_circle2)

        

        #for i in range(1,pointcount2+1):
        #        image2 = cv2.circle(image2,(int(pts_x2[i-1]),int(pts_y2[i-1])),int(pts_w2[i-1]),(0,255,0),1)
        #        cv2.putText(image2, f'{i}', (int(pts_x2[i-1])+int(pts_w2[i-1]),int(pts_y2[i-1])+int(pts_h2[i-1])-30) , cv2.FONT_HERSHEY_SIMPLEX, 0.9, (36,255,12), 1)
        lb_Result_img.clear()
        lb_Result_img.append(tk.Label(pop_cam1_result, image=photo_image1))
        lb_Result_img[0].image = photo_image1  # ÀÌ¹ÌÁö °´Ã¼¸¦ Àü¿ª º¯¼ö·Î ÀúÀå
        lb_Result_img[0].grid(row=1, column=1)
        
        lb_Result_img.clear()
        lb_Result_img2.append(tk.Label(pop_cam2_result, image=photo_image2))
        lb_Result_img2[0].image = photo_image2  # ÀÌ¹ÌÁö °´Ã¼¸¦ Àü¿ª º¯¼ö·Î ÀúÀå
        lb_Result_img2[0].grid(row=1, column=2)
    
    label = tk.Label(result_popup, text=f"CAM1-1 COUNT: {label_list_result_cnt[0]} (OK : {label_list_result_OK_cnt[0]}) (NG : {label_list_result_NG_cnt[0]}), CAM1-2 COUNT: {label_list_result_cnt[1]}  (OK : {label_list_result_OK_cnt[1]}) (NG : {label_list_result_NG_cnt[1]})")
    label.grid(column=1,columnspan=3, row=3, padx=0, pady=0)
    label = tk.Label(result_popup, text=f"CAM2-1 COUNT: {label_list_result2_cnt[0]} (OK : {label_list_result2_OK_cnt[0]}) (NG : {label_list_result2_NG_cnt[0]}), CAM2-2 COUNT: {label_list_result2_cnt[1]}  (OK : {label_list_result2_OK_cnt[1]}) (NG : {label_list_result2_NG_cnt[1]})")
    label.grid(column=1,columnspan=3, row=4, padx=0, pady=0)
    
    def Clear_value():
        global result_view_image1,image1,photo_image1,image_cv1,image_cv1_cropped
        global result_view_image2,image2,photo_image2,image_cv2,image_cv2_cropped
        
        label.configure(image=None)
        
        result_view_image1=None
        result_view_image2=None
        image1=None
        image_cv1=None
        image_cv1_cropped =None
        photo_image1=None
        
        image2=None
        image_cv2=None
        image_cv2_cropped =None
        photo_image2=None
        print("Clear")
        
    Clear_value()
    result_popup.after(4000, close_popup)




def btn_git_upndown(btnType):
    github_repo_owner = 'pmanone'
    github_repo_name = 'damper'
    github_token = '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'
    headers = {'Authorization': f'token {github_token}'}
    download_dir = 'downloads'
    upload_dir = 'uploads'
    api_url = f'https://api.github.com/repos/{github_repo_owner}/{github_repo_name}'
    root_folder = '.'

    if btnType == "down":
        target_files = ['AITVIS.py', 'DAMPER_1_1_1.h5', 'DAMPER_1_1_2.h5', 'DAMPER_1_2_1.h5', 'DAMPER_1_2_2.h5', 'DAMPER_2_1_1.h5', 'DAMPER_2_1_2.h5', 'DAMPER_2_2_1.h5', 'DAMPER_2_2_2.h5']

        download_repository_contents(api_url, headers, download_dir, target_filenames=target_files)
    elif btnType == "up":
        upload_repository_contents(api_url, headers, root_folder)

def create_folder(api_url, headers, folder_path):
    # GitHub에 폴더 생성
    payload = {
        'message': f'Create folder {folder_path}',
        'content': '',  # 빈 문자열을 전달하여 폴더 생성
        'committer': {
            'name': 'pmanone',  # 여기에 본인의 GitHub 사용자명 입력
            'email': 'pmanone@naver.com'  # 여기에 본인의 이메일 주소 입력
        }
    }
    folder_path = folder_path+ "\damper"
    response = requests.put(f'{api_url}/contents/{folder_path}', headers=headers, json=payload)

    if response.status_code == 201:
        print(f'{folder_path} folder created successfully')
    else:
        print(f'Failed to create {folder_path} folder')

def get_file_sha(api_url, headers, filename):
    # 파일 정보 가져오기
    response = requests.get(f'{api_url}/contents/{filename}', headers=headers)

    if response.status_code == 200:
        data = response.json()
        return data.get('sha')
    else:
        return None

def upload_file(api_url, headers, filename, content, sha=None):
    # 파일 내용을 base64로 인코딩
    encoded_content = base64.b64encode(content).decode('utf-8')

    # GitHub에 파일 업로드
    payload = {
        'message': f'Upload {filename}',
        'content': encoded_content,
        'sha': sha,  # 존재하는 파일을 업데이트할 때 sha를 제공
        'committer': {
            'name': 'Your GitHub Username',  # 여기에 본인의 GitHub 사용자명 입력
            'email': 'your.email@example.com'  # 여기에 본인의 이메일 주소 입력
        }
    }
    response = requests.put(f'{api_url}/contents/{filename}', headers=headers, json=payload)

    if response.status_code == 201:
        print(f'{filename} uploaded successfully')
    else:
        print(f'Failed to upload {filename}')


def upload_directory(api_url, headers, folder_path, root_folder):
    for root, dirs, files in os.walk(folder_path):
        for filename in files:
            relative_path = os.path.relpath(os.path.join(root, filename), root_folder)
            file_path = os.path.join(root, filename)

            # 파일 내용 읽기
            with open(file_path, 'rb') as file:
                file_content = file.read()

            
            sha = get_file_sha(api_url, headers, relative_path)

            
            upload_file(api_url, headers, relative_path, file_content, sha)

def upload_repository_contents(api_url, headers, root_folder):
    
    files_and_folders = ['AITVIS.py', 'DAMPER_1_1_1.h5', 'DAMPER_1_1_2.h5', 'DAMPER_1_2_1.h5', 'DAMPER_1_2_2.h5', 'DAMPER_2_1_1.h5', 'DAMPER_2_1_2.h5', 'DAMPER_2_2_1.h5', 'DAMPER_2_2_2.h5', 'result\liveimg'] #damper
    #files_and_folders = ['AITVIS.py', 'DAMPER_1_1_1.h5', 'DAMPER_1_1_2.h5', 'DAMPER_1_2_1.h5', 'DAMPER_1_2_2.h5', 'DAMPER_2_1_1.h5', 'DAMPER_2_1_2.h5', 'DAMPER_2_2_1.h5', 'DAMPER_2_2_2.h5', 'result\liveimg'] #MQ4PE_L_R

    for item in files_and_folders:
        item_path = os.path.join(item)

        if os.path.isfile(item_path):  # 파일 처리
            with open(item_path, 'rb') as file:
                file_content = file.read()

            # 기존 파일의 sha 값 가져오기
            sha = get_file_sha(api_url, headers, item)

            # 파일 업로드
            upload_file(api_url, headers, item, file_content, sha)
        elif os.path.isdir(item_path):  # 폴더 처리
            # 폴더 생성
            create_folder(api_url, headers, item)
            # 폴더 내 파일 업로드
            upload_directory(api_url, headers, item_path, root_folder)



def download_repository_contents(api_url, headers, download_dir, path='', target_filenames=None):
    # 저장소의 트리를 가져오기
    tree_response = requests.get(f'{api_url}/git/trees/main?recursive=1', headers=headers)

    if tree_response.status_code == 200:
        tree_data = tree_response.json()

        # 트리에서 각 파일 및 폴더의 정보 추출
        for item in tree_data['tree']:
            item_path = item['path']

            if item_path.startswith(path):  # 지정한 경로의 파일 및 폴더만 처리
                relative_path = os.path.relpath(item_path, path)

                if item['type'] == 'blob' and (not target_filenames or relative_path in target_filenames):  # 파일 처리
                    raw_url = item['url']  # raw URL을 가져오는 대신, 여기서는 API에서 제공하는 URL을 사용합니다.
                    download_file(api_url, headers, download_dir, relative_path, raw_url)

                elif item['type'] == 'tree':  # 폴더 처리 (재귀 호출)
                    download_repository_contents(api_url, headers, download_dir, item_path, target_filenames)

    else:
        print(f'Failed to get tree data for the repository')


def download_file(api_url, headers, download_dir, relative_path, raw_url):
    # GitHub에서 파일 내용 가져오기
    response = requests.get(raw_url, headers=headers)
    file_content = response.content

    # 파일 내용을 다운로드 디렉토리에 저장 (폴더 구조 유지)
    file_path = os.path.join(download_dir, relative_path)
    os.makedirs(os.path.dirname(file_path), exist_ok=True)
    with open(file_path, 'wb') as file:
        file.write(file_content)
    
    os.chmod(file_path, 0o777)
    print(f'{relative_path} downloaded successfully')

#image processing
def train_svm(X, y):
    model = svm.SVC(kernel='linear')
    model.fit(X, y)
    return model

def apply_svm(svm, samples):
    predictions = svm.predict(samples)
    return predictions


def pointSetting(cnt,isxy,value,id):
    #포인트 변경시마다 저장

    value = int(value)
    if isxy=="x":
        pts_x[cnt-1] = value
    elif isxy=="y":
        pts_y[cnt-1] = value
    elif isxy=="w":
        pts_w[cnt-1] = value
    elif isxy=="h":
        pts_h[cnt-1] = value
    elif isxy=="x2":
        pts_x2[cnt-1] = value
    elif isxy=="y2":
        pts_y2[cnt-1] = value
    elif isxy=="w2":
        pts_w2[cnt-1] = value
    elif isxy=="h2":
        pts_h2[cnt-1] = value

    with open('./ptsx.pickle', 'wb') as f:
        pickle.dump(pts_x, f)

    with open('./ptsy.pickle', 'wb') as f:
        pickle.dump(pts_y, f)

    with open('./ptsw.pickle', 'wb') as f:
        pickle.dump(pts_w, f)

    with open('./ptsh.pickle', 'wb') as f:
        pickle.dump(pts_h, f)

    with open('./ptsx2.pickle', 'wb') as f:
        pickle.dump(pts_x2, f)

    with open('./ptsy2.pickle', 'wb') as f:
        pickle.dump(pts_y2, f)

    with open('./ptsw2.pickle', 'wb') as f:
        pickle.dump(pts_w2, f)

    with open('./ptsh2.pickle', 'wb') as f:
        pickle.dump(pts_h2, f)
       
def btn_setPoint(cnt,btn,camType):
    if camType == "CAM1":
        for i in range(1,pointcount+1):
            data = cv2.mean(cv2.cvtColor(bgrroi[i-1][1:,1:] , cv2.COLOR_BGR2HSV))
            points_std[i-1] = np.append(points_std[i-1],int(data[2]))
            points_std[i-1] = [i for i in points_std[i-1][1:]]
           
            blue_threshold = 200
            green_threshold = 200
            red_threshold = 200
            bgr_threshold = [blue_threshold, green_threshold, red_threshold]

            if Ck_inspType_Var2[i-1].get() == 1:
                thresholds = (bgrroi[i-1][:,:,0] < bgr_threshold[0]) \
                | (bgrroi[i-1][:,:,1] < bgr_threshold[1]) \
                | (bgrroi[i-1][:,:,2] < bgr_threshold[2])
                bgrroi[i-1][thresholds] = [0,0,0]
                points_roi_std[i-1] =int(np.mean(bgrroi[i-1]))

   
            img_mean = np.zeros(bgrroi[i-1].shape, dtype=np.uint8)
            img_mean[:] = (data[0], data[1], data[2])
            #print(int(data[2]))
            #+np.median(cv2.cvtColor(bgrroi[0][1:,1:] , cv2.COLOR_BGR2HSV)[int(pts_h[1])])+np.median(cv2.cvtColor(bgrroi[0][1:,1:] , cv2.COLOR_BGR2HSV)[int(pts_h[2])])

            btn_Pointdis[i-1].config(text=str(int(data[2])))
                                            #+np.median(cv2.cvtColor(bgrroi[0][1:,1:] , cv2.COLOR_BGR2HSV)[int(pts_h[1])])
                                            #+np.median(cv2.cvtColor(bgrroi[0][1:,1:] , cv2.COLOR_BGR2HSV)[int(pts_h[2])]))
            #print(points_std[i-1])
   
    if camType == "CAM2":
        for i in range(1,pointcount2+1):
            data2 = cv2.mean(cv2.cvtColor(bgrroi2[i-1][1:,1:] , cv2.COLOR_BGR2HSV))
            points_std2[i-1] = np.append(points_std2[i-1],int(data2[2]))
            points_std2[i-1] = [i for i in points_std2[i-1][1:]]
            print("settinbg")
            print(points_std2)
            blue_threshold = 200
            green_threshold = 200
            red_threshold = 200
            bgr_threshold = [blue_threshold, green_threshold, red_threshold]

            if Ck2_inspType_Var2[i-1].get() == 1:
                thresholds = (bgrroi2[i-1][:,:,0] < bgr_threshold[0]) \
                | (bgrroi2[i-1][:,:,1] < bgr_threshold[1]) \
                | (bgrroi2[i-1][:,:,2] < bgr_threshold[2])
                bgrroi2[i-1][thresholds] = [0,0,0]
                points_roi_std2[i-1] =int(np.mean(bgrroi2[i-1]))
   
            img_mean2 = np.zeros(bgrroi2[i-1].shape, dtype=np.uint8)
            img_mean2[:] = (data2[0], data2[1], data2[2])

            btn_Pointdis2[i-1].config(text=str(int(data2[2])))

   
def btn_pt_set(btn,btnType):


    with open('./pointcnt.pickle', 'wb') as f:
        pickle.dump(txt_Set_Pts.get(), f)

    with open('./pointcnt2.pickle', 'wb') as f:
        pickle.dump(txt_Set_Pts2.get(), f)

    restart()

def btn_file_move(btn,stattype,camNum,num):
    
    if camNum == 1:
        #파일 이동/삭제 관련 
        #init 은 result image 삭제

        if stattype == "good":
            src_file_path = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM1/'+str(num)+'/'
            dst_folder_path = os.getcwd() +'/dataset/cam1/'+str(num)+'/good/'
            for filename in os.listdir(src_file_path):
                src_path = os.path.join(src_file_path, filename)
                dst_path = os.path.join(dst_folder_path, filename)
                shutil.copy(src_path, dst_path)
        elif stattype == "bad":
            src_file_path = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM1/'+str(num)+'/'
            dst_folder_path = os.getcwd() +'/dataset/cam1/'+str(num)+'/bad/'
            for filename in os.listdir(src_file_path):
                src_path = os.path.join(src_file_path, filename)
                dst_path = os.path.join(dst_folder_path, filename)
                shutil.copy(src_path, dst_path)
        elif stattype == "init":
            folder_path  = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM1/'+str(num)+'/'
            for filename in os.listdir(folder_path):
                file_path = os.path.join(folder_path, filename)
                if os.path.isfile(file_path) or os.path.islink(file_path):
                    os.unlink(file_path)
    elif camNum == 2:
        #파일 이동/삭제 관련 
        #init 은 result image 삭제

        if stattype == "good":
            src_file_path = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(num)+'/'
            dst_folder_path = os.getcwd() +'/dataset/cam2/'+str(num)+'/good/'
            for filename in os.listdir(src_file_path):
                src_path = os.path.join(src_file_path, filename)
                dst_path = os.path.join(dst_folder_path, filename)
                shutil.copy(src_path, dst_path)
        elif stattype == "bad":
            src_file_path = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(num)+'/'
            dst_folder_path = os.getcwd() +'/dataset/cam2/'+str(num)+'/bad/'
            for filename in os.listdir(src_file_path):
                src_path = os.path.join(src_file_path, filename)
                dst_path = os.path.join(dst_folder_path, filename)
                shutil.copy(src_path, dst_path)
        elif stattype == "init":
            folder_path  = os.getcwd() + '/result/liveImg/'+str(datetime.now().strftime("%Y%m%d"))+'/CAM2/'+str(num)+'/'
            for filename in os.listdir(folder_path):
                file_path = os.path.join(folder_path, filename)
                if os.path.isfile(file_path) or os.path.islink(file_path):
                    os.unlink(file_path)

    #elif camNum == 2:



def Getcol_set(btn,btnType):
    roiMean = bgrroi
    roiMean2 = bgrroi2
    print("d")
           
def btnNumSet(btn,btnType):
    print("btnNumset")

def set_authConfirm_color(color):
    btn_Auth.config(bg=color)   
   
#restart
def restart():
    print("AutoRes is starting")
   
   
    executable = os.sys.executable
    args = sys.argv[:]
    args.insert(0, sys.executable)
    time.sleep(1)
    print("Respawning")
    os.execvp(executable, args)
def popup_Auth():
    global authConfirm
    global passwd
    global popup_list

    p_Auth = tk.Toplevel(root)
    
    #popup_list.append(p_Auth)
    p_Auth.title("AUTH")
    
    p_Auth.geometry("+{}+{}".format(root.winfo_rootx() + 0, root.winfo_rooty() + 0))
    
    def close_popup():
        p_Auth.destroy()

    def button_clicked(value):
        current_value = label.cget("text")  # ÇöÀç ÅØ½ºÆ® °ªÀ» °¡Á®¿È
        if len(current_value) < 4:  # ÇöÀç ÅØ½ºÆ® °ªÀÇ ±æÀÌ°¡ 4 ¹Ì¸¸ÀÎ °æ¿ì¿¡¸¸ ¼ýÀÚ Ãß°¡
            label.config(text=current_value+str(value))

            #label.config(text=current_value + str(value))

            if len(current_value) == 3:
                if current_value+str(value) == str(passwd):
                    global authConfirm
                    authConfirm = True
                    print("Authentication successful")
                    reset_label()
                    set_button_color("green")
                    for i in range(1,pointcount+1):
                        pts_sh[i-1].config(state="normal")
                        pts_sw[i-1].config(state="normal")
                        pts_sx[i-1].config(state="normal")
                        pts_sy[i-1].config(state="normal")

                    for i in range(1,pointcount2+1):
                        pts_sh2[i-1].config(state="normal")
                        pts_sw2[i-1].config(state="normal")
                        pts_sx2[i-1].config(state="normal")
                        pts_sy2[i-1].config(state="normal")
                    
                    close_popup()

                else:
                    authConfirm = False
                    print("Authentication failed")
                    reset_label()
                    set_button_color("red")

                    for i in range(1,pointcount+1):
                        pts_sh[i-1].config(state="disabled")
                        pts_sw[i-1].config(state="disabled")
                        pts_sx[i-1].config(state="disabled")
                        pts_sy[i-1].config(state="disabled")

                    for i in range(1,pointcount2+1):
                        pts_sh2[i-1].config(state="disabled")
                        pts_sw2[i-1].config(state="disabled")
                        pts_sx2[i-1].config(state="disabled")
                        pts_sy2[i-1].config(state="disabled")
                    popups_to_close = []  # ´ÝÀ» ÆË¾÷ Ã¢À» ÀúÀåÇÒ ¸®½ºÆ®
                    for popup in popup_list:
                        if popup.winfo_exists():  # ÆË¾÷ Ã¢ÀÌ ¿­·ÁÀÖ´ÂÁö È®ÀÎ
                            popups_to_close.append(popup)  # ´ÝÀ» ÆË¾÷ Ã¢ ÀúÀå
    
                    # ¹Ýº¹¹®ÀÌ Á¾·áµÈ ÈÄ¿¡ ÆË¾÷ Ã¢À» ´ÝÀ½
                    for popup in popups_to_close:
                        popup.destroy()
    
                    popup_list.clear()  # ÆË¾÷ ¸®½ºÆ® ÃÊ±âÈ­

    def show_number():
        current_value = label.cget("text")  # ÇöÀç ÅØ½ºÆ® °ªÀ» °¡Á®¿È
        if len(current_value) < 4:  # ÇöÀç ÅØ½ºÆ® °ªÀÇ ±æÀÌ°¡ 4 ¹Ì¸¸ÀÎ °æ¿ì¿¡¸¸ ½ÇÁ¦ ¼ýÀÚ·Î º¯°æ
            label.config(text=current_value[:-1] + str(value))

    def reset_label():
        label.config(text="")  # label ÃÊ±âÈ­

    def set_button_color(color):
        btn_Auth.config(bg=color)



    label = tk.Label(p_Auth, text="")
    label.grid(column=1, columnspan=3,row=1, padx=0, pady=0)

    button_1 = tk.Button(p_Auth, text="1", command=lambda:button_clicked(1), width=10, height=3)
    button_1.grid(column=1, row=2, padx=0, pady=0)

    
    button_2 = tk.Button(p_Auth, text="2", command=lambda:button_clicked(2), width=10, height=3)
    button_2.grid(column=2, row=2, padx=0, pady=0)

    
    button_3 = tk.Button(p_Auth, text="3", command=lambda:button_clicked(3), width=10, height=3)
    button_3.grid(column=3, row=2, padx=0, pady=0)

    
    button_4 = tk.Button(p_Auth, text="4", command=lambda:button_clicked(4), width=10, height=3)
    button_4.grid(column=1, row=3, padx=0, pady=0)

    
    button_5 = tk.Button(p_Auth, text="5", command=lambda:button_clicked(5), width=10, height=3)
    button_5.grid(column=2, row=3, padx=0, pady=0)

    
    button_6 = tk.Button(p_Auth, text="6", command=lambda:button_clicked(6), width=10, height=3)
    button_6.grid(column=3, row=3, padx=0, pady=0)

    
    button_7 = tk.Button(p_Auth, text="7", command=lambda:button_clicked(7), width=10, height=3)
    button_7.grid(column=1, row=4, padx=0, pady=0)

    
    button_8 = tk.Button(p_Auth, text="8", command=lambda:button_clicked(8), width=10, height=3)
    button_8.grid(column=2, row=4, padx=0, pady=0)
    
    button_9 = tk.Button(p_Auth, text="9", command=lambda:button_clicked(9), width=10, height=3)
    button_9.grid(column=3, row=4, padx=0, pady=0)

    button_re = tk.Button(p_Auth, text="RESET", command=reset_label, width=10, height=3)
    button_re.grid(column=1, row=5, padx=0, pady=0)

    button_0 = tk.Button(p_Auth, text="0", command=lambda:button_clicked(0), width=10, height=3)
    button_0.grid(column=2, row=5, padx=0, pady=0)

def popup_ModelChage():
    global authConfirm
    global passwd
    global popup_list
    
    if not authConfirm:
        return
    
    
    p_change = tk.Toplevel(root)
    
    p_change.title("Model Change")

    p_change.geometry("+{}+{}".format(root.winfo_rootx() + 0, root.winfo_rooty() + 0))

    def close_popup():
        p_change.destroy()

    def copy_folder(source_folder, destination_folder):
        if os.path.exists(destination_folder):
            shutil.rmtree(destination_folder)  # ±âÁ¸ÀÇ ¸ñÀûÁö Æú´õ°¡ ÀÖÀ¸¸é Á¦°Å
        shutil.copytree(source_folder, destination_folder)
    def check_and_copy_files(source_folder, destination_folder, files):
        # ¼Ò½º Æú´õ¿Í ¸ñÀûÁö Æú´õ È®ÀÎ
        if not os.path.exists(source_folder):
            print("The source folder does not exist.")
            return
        if not os.path.exists(destination_folder):
            os.makedirs(destination_folder)

        for file in files:
            source_file = os.path.join(source_folder, file)
            destination_file = os.path.join(destination_folder, file)
        
            # ÆÄÀÏÀÌ Á¸ÀçÇÏ´ÂÁö È®ÀÎÇÏ°í º¹»ç
            if os.path.isfile(source_file):
                shutil.copy2(source_file, destination_file)
                print(f"Failed to copy {file}.")
            else:
                print(f"{file} does not exist.")

    def read_data_from_file(filename):
        try:
            with open(filename, "r") as file:
                data = file.read().splitlines()
            return data
        except FileNotFoundError:
            return []

    def write_data_to_file(filename, data):
        with open(filename, "w") as file:
            file.write('\n'.join(data))
            close_popup()

    def add_item():
        item = entry.get()
        if item:
            listbox.insert(tk.END, item)
            entry.delete(0, tk.END)
            data.append(item)
            write_data_to_file(filename, data)

            current_directory = os.getcwd()
            datasetfoldername ="ModelData//" + item + "//Dataset"
            ptsFilename ="ModelData//" + item + "//Pts"
            destination_folder = os.path.join(current_directory, datasetfoldername)
            destination_ptsFile = os.path.join(current_directory, ptsFilename)

            source_folder = os.path.join(current_directory,"dataset")
            files_to_copy = ['btn_Pointdis.pickle', 'pointcnt.pickle', 'pointcnt2.pickle','ptsh.pickle','ptsh2.pickle','ptsw.pickle','ptsw2.pickle','ptsx.pickle','ptsx2.pickle','ptsy.pickle','ptsy2.pickle','CAM1_1.h5','CAM2_1.h5']

            copy_folder(source_folder, destination_folder)
            check_and_copy_files(current_directory, destination_ptsFile,files_to_copy)


    def delete_item():
        selected_index = listbox.curselection()
        if selected_index:
            index = int(selected_index[0])  # Æ©ÇÃ¿¡¼­ Á¤¼ö °ª ÃßÃâ
            item = listbox.get(index)
            listbox.delete(index)
            data.remove(item)
            write_data_to_file(filename, data)
    def item_selected(event):
        selected_items = listbox.curselection()
        if selected_items:
            index = selected_items[0]
            item = listbox.get(index)
            response = messagebox.askquestion("Confirmation", "Do you want to change to '{}'?".format(item))
            if response == 'yes':
                #pts_sh[0].event_generate('<<ScaleChanged>>')

                #1.file move (Dataset -> exdata)
                current_directory = os.getcwd()
                filename_selected = current_directory + "/selected_data.txt"
                ex_data = read_data_from_file(filename_selected)
                
                if ex_data != []:
                    datafoldername ="ModelData//" + str(ex_data[0]) + "//Dataset"
                    ptsfoldername ="ModelData//" + str(ex_data[0]) + "//Pts"
                    destination_folder = os.path.join(current_directory, datafoldername)
                    destination_ptsFile = os.path.join(current_directory, ptsfoldername)
                    files_to_copy = ['btn_Pointdis.pickle', 'pointcnt.pickle', 'pointcnt2.pickle','ptsh.pickle','ptsh2.pickle','ptsw.pickle','ptsw2.pickle','ptsx.pickle','ptsx2.pickle','ptsy.pickle','ptsy2.pickle','CAM1_1.h5','CAM2_1.h5']

                    source_folder = os.path.join(current_directory,"dataset")
                    copy_folder(source_folder, destination_folder)
                    check_and_copy_files(current_directory, destination_ptsFile,files_to_copy)

                #2.file move (FILE -> Dataset)
                current_directory = os.getcwd()
                datafoldername ="dataset"
                destination_folder = os.path.join(current_directory, datafoldername)
                destination_ptsFile = current_directory
                files_to_copy = ['btn_Pointdis.pickle', 'pointcnt.pickle', 'pointcnt2.pickle','ptsh.pickle','ptsh2.pickle','ptsw.pickle','ptsw2.pickle','ptsx.pickle','ptsx2.pickle','ptsy.pickle','ptsy2.pickle','CAM1_1.h5','CAM2_1.h5']

                source_folder = os.path.join(current_directory,"ModelData//"+ str(item) +"//Dataset")
                source_pts_folder = os.path.join(current_directory,"ModelData//"+ str(item) +"//Pts")
                copy_folder(source_folder, destination_folder)
                check_and_copy_files(source_pts_folder, destination_ptsFile,files_to_copy)


                print("Selected Item:", item)
                
                filename_selected = current_directory + "/selected_data.txt"
                # ¼±ÅÃµÈ ¾ÆÀÌÅÛÀ» data.txt ÆÄÀÏ¿¡ ÀúÀå
                write_data_to_file(filename_selected, [item])

                os.system('sudo reboot')
            else:
                print("d")
                # ÀÌÀü¿¡ ¼±ÅÃÇÑ ¾ÆÀÌÅÛÀ¸·Î Ä¿¼­ ÀÌµ¿
                #filename = "D:/test/xam_app/VISIONCAMERA/VISIONCAMERA/data.txt"
                #filename_selected = "D:/test/xam_app/VISIONCAMERA/VISIONCAMERA/selected_data.txt"
                #data = read_data_from_file(filename)
                #
                #selected_data = read_data_from_file(filename_selected)
                #if selected_data:
                #    selected_item = selected_data[0]
                #    if selected_item in data:
                #        selected_index = data.index(selected_item)
                #        if selected_index >= 0 and selected_index < listbox.size():
                #            listbox.select_set(selected_index)
                
                #close_popup()



    # Á¦¸ñ ¶óº§
    title_label = tk.Label(p_change, text="Model Change", font=("Helvetica", 16, "bold"))
    title_label.grid(row=0, column=0, columnspan=4, pady=10)

    # ÀÔ·Â ¶óº§°ú ¿£Æ®¸®
    input_label = tk.Label(p_change, text="item:", font=("Helvetica", 12))
    input_label.grid(row=1, column=0,columnspan=1, sticky="e", padx=5, pady=5)

    entry = tk.Entry(p_change, font=("Helvetica", 12))
    entry.grid(row=1, column=1,columnspan=3, sticky="w", padx=5, pady=5)

    # Ãß°¡ ¹öÆ°
    add_button = tk.Button(p_change, text="Add", command=add_item, font=("Helvetica", 12), width=10, height=2)
    add_button.grid(row=2, column=0, columnspan=2, padx=10, pady=5)

    # »èÁ¦ ¹öÆ°
    delete_button = tk.Button(p_change, text="Delete", command=delete_item, font=("Helvetica", 12), width=10, height=2)
    delete_button.grid(row=2, column=2, columnspan=2, padx=10, pady=5)

    # ¸®½ºÆ® ¹Ú½º
    listbox = tk.Listbox(p_change, font=("Helvetica", 12), width=25)
    listbox.grid(row=4, column=0, columnspan=4, padx=10, pady=5)

    listbox.bind("<<ListboxSelect>>", item_selected)


    file_directory = os.getcwd()
    filename = file_directory + "/data.txt"
    filename_selected = file_directory + "/selected_data.txt"
    print(filename_selected)
    data = read_data_from_file(filename)

    for item in data:
        listbox.insert(tk.END, item)

    selected_data = read_data_from_file(filename_selected)
    if selected_data:
        selected_item = selected_data[0]
        if selected_item in data:
            selected_index = data.index(selected_item)
            if selected_index >= 0 and selected_index < listbox.size():
                listbox.select_clear(0, tk.END)
                listbox.select_set(selected_index)



    popup_list.append(p_change)
    p_change.mainloop()

def Range_popup(numi,camType):
    global popup_created, ok_img, ng_img
    lb_Result_img=[]
    lb_Result_img2=[]

    if not popup_created:
        popup = tk.Toplevel(root)
        popup.title("팝업")
        
        popup.geometry("+{}+{}".format(root.winfo_rootx() + 445, root.winfo_rooty() + 95))

        pop_cam1_result = tk.LabelFrame(popup,text="CAM1_RESULT")
        pop_cam1_result.grid(column=1, row=1, padx=0, pady=0)
        pop_cam2_result = tk.LabelFrame(popup,text="CAM2_RESULT")
        pop_cam2_result.grid(column=1, row=2, padx=0, pady=0)

        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rrl",value,f"pt{i}_rrl")))
        lb_Result_img[0].grid(row=0, column=0)
        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rrh",value,f"pt{i}_rrh")))
        lb_Result_img[1].grid(row=0, column=1)
        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rgl",value,f"pt{i}_rgl")))
        lb_Result_img[2].grid(row=1, column=0)
        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rgh",value,f"pt{i}_rgh")))
        lb_Result_img[3].grid(row=1, column=1)
        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rbl",value,f"pt{i}_rbl")))
        lb_Result_img[4].grid(row=2, column=0)
        lb_Result_img.append(tk.Scale( pop_cam1_result, from_ = 0, to = 255, orient = "horizontal",command = lambda value,i=numi: RangepointSetting(i,"rbh",value,f"pt{i}_rbh")))
        lb_Result_img[5].grid(row=2, column=1)


        popup_created = True
    
        def on_close():
            global popup_created, ok_img, ng_img
            popup_created = False
            ok_img = None
            ng_img = None
            popup.destroy()

        def RangepointSetting(cnt,isxy,value,id):
            #포인트 변경시마다 저장
            if camType == "CAM1":
                value = int(value)
                if isxy=="rrl":
                    pts_rrl[cnt-1] = value
                elif isxy=="rrh":
                    pts_rrh[cnt-1] = value
                elif isxy=="rgl":
                    pts_rgl[cnt-1] = value
                elif isxy=="rgh":
                    pts_rgh[cnt-1] = value
                elif isxy=="rbl":
                    pts_rbl[cnt-1] = value
                elif isxy=="rbh":
                    pts_rbh[cnt-1] = value
                
                
                with open('./pts_rrl.pickle', 'wb') as f:
                    pickle.dump(pts_rrl, f)
                
                with open('./pts_rrh.pickle', 'wb') as f:
                    pickle.dump(pts_rrh, f)
                
                with open('./pts_rgl.pickle', 'wb') as f:
                    pickle.dump(pts_rgl, f)
                
                with open('./pts_rgh.pickle', 'wb') as f:
                    pickle.dump(pts_rgh, f)
                
                with open('./pts_rbl.pickle', 'wb') as f:
                    pickle.dump(pts_rbl, f)
                
                with open('./pts_rbh.pickle', 'wb') as f:
                    pickle.dump(pts_rbh, f)
            else:
                value = int(value)
                if isxy=="rrl":
                    pts2_rrl[cnt-1] = value
                elif isxy=="rrh":
                    pts2_rrh[cnt-1] = value
                elif isxy=="rgl":
                    pts2_rgl[cnt-1] = value
                elif isxy=="rgh":
                    pts2_rgh[cnt-1] = value
                elif isxy=="rbl":
                    pts2_rbl[cnt-1] = value
                elif isxy=="rbh":
                    pts2_rbh[cnt-1] = value
                
                
                with open('./pts2_rrl.pickle', 'wb') as f:
                    pickle.dump(pts2_rrl, f)
                
                with open('./pts2_rrh.pickle', 'wb') as f:
                    pickle.dump(pts2_rrh, f)
                
                with open('./pts2_rgl.pickle', 'wb') as f:
                    pickle.dump(pts2_rgl, f)
                
                with open('./pts2_rgh.pickle', 'wb') as f:
                    pickle.dump(pts2_rgh, f)
                
                with open('./pts2_rbl.pickle', 'wb') as f:
                    pickle.dump(pts2_rbl, f)
                
                with open('./pts2_rbh.pickle', 'wb') as f:
                    pickle.dump(pts2_rbh, f)

        popup.protocol("WM_DELETE_WINDOW", on_close)

        popup.geometry("300x300")

        def update_images():
            print("d")
        update_images()

def popup():
    global popup_created, ok_img, ng_img
    lb_Result_img=[]
    lb_Result_img2=[]

    if not popup_created:
        popup = tk.Toplevel(root)
        popup.title("팝업")
        
        popup.geometry("+{}+{}".format(root.winfo_rootx() + 445, root.winfo_rooty() + 95))

        pop_cam1_result = tk.LabelFrame(popup,text="CAM1_RESULT")
        pop_cam1_result.grid(column=1, row=1, padx=0, pady=0)
        pop_cam2_result = tk.LabelFrame(popup,text="CAM2_RESULT")
        pop_cam2_result.grid(column=1, row=2, padx=0, pady=0)


        Okimg = Image.open(os.getcwd()+'/img/OK.JPG')
        Okimg = Okimg.resize((33, 33), Image.LANCZOS)
        ok_img = ImageTk.PhotoImage(Okimg)

        NGimg = Image.open(os.getcwd()+'/img/NG.JPG')
        NGimg = NGimg.resize((33, 33), Image.LANCZOS)
        ng_img = ImageTk.PhotoImage(NGimg)
        

        
        for i in range(1,pointcount+1):
            lb_Result_img.append(tk.Label(pop_cam1_result, image=ok_img))
            if i == 1:
                lb_Result_img[i-1].grid(row=1, column=1)
            elif i == 2:
                lb_Result_img[i-1].grid(row=1, column=2)
            elif i == 3:
                lb_Result_img[i-1].grid(row=1, column=3)
            elif i == 4:
                lb_Result_img[i-1].grid(row=1, column=4)
            elif i == 5:
                lb_Result_img[i-1].grid(row=1, column=5)
            elif i == 6:
                lb_Result_img[i-1].grid(row=1, column=6)
            elif i == 7:
                lb_Result_img[i-1].grid(row=1, column=7)
            elif i == 8:
                lb_Result_img[i-1].grid(row=1, column=8)
            elif i == 9:
                lb_Result_img[i-1].grid(row=2, column=1)
            elif i == 10:
                lb_Result_img[i-1].grid(row=2, column=2)
            elif i == 11:
                lb_Result_img[i-1].grid(row=2, column=3)
            elif i == 12:
                lb_Result_img[i-1].grid(row=2, column=4)
            elif i == 13:
                lb_Result_img[i-1].grid(row=2, column=5)
            elif i == 14:
                lb_Result_img[i-1].grid(row=2, column=6)
            elif i == 15:
                lb_Result_img[i-1].grid(row=2, column=7)
            elif i == 16:
                lb_Result_img[i-1].grid(row=2, column=8)

        for i in range(1,pointcount2+1):
            lb_Result_img2.append(tk.Label(pop_cam2_result, image=ok_img))
            if i == 1:
                lb_Result_img2[i-1].grid(row=1, column=1)
            elif i == 2:
                lb_Result_img2[i-1].grid(row=1, column=2)
            elif i == 3:
                lb_Result_img2[i-1].grid(row=1, column=3)
            elif i == 4:
                lb_Result_img2[i-1].grid(row=1, column=4)
            elif i == 5:
                lb_Result_img2[i-1].grid(row=1, column=5)
            elif i == 6:
                lb_Result_img2[i-1].grid(row=1, column=6)
            elif i == 7:
                lb_Result_img2[i-1].grid(row=1, column=7)
            elif i == 8:
                lb_Result_img2[i-1].grid(row=1, column=8)
            elif i == 9:
                lb_Result_img2[i-1].grid(row=2, column=1)
            elif i == 10:
                lb_Result_img2[i-1].grid(row=2, column=2)
            elif i == 11:
                lb_Result_img2[i-1].grid(row=2, column=3)
            elif i == 12:
                lb_Result_img2[i-1].grid(row=2, column=4)
            elif i == 13:
                lb_Result_img2[i-1].grid(row=2, column=5)
            elif i == 14:
                lb_Result_img2[i-1].grid(row=2, column=6)
            elif i == 15:
                lb_Result_img2[i-1].grid(row=2, column=7)
            elif i == 16:
                lb_Result_img2[i-1].grid(row=2, column=8)


        popup_created = True
    
        def on_close():
            global popup_created, ok_img, ng_img
            popup_created = False
            ok_img = None
            ng_img = None
            popup.destroy()

        popup.protocol("WM_DELETE_WINDOW", on_close)

        popup.geometry("300x300")

        def update_images():
            if len(label_list_result) > 0:
                for i in range(1,pointcount+1):
                    if  label_list_result[i-1] == 0:
                        lb_Result_img[i-1].configure(image=ng_img)
                    elif label_list_result[i-1] == 1:
                        lb_Result_img[i-1].configure(image=ok_img)


                for i in range(1,pointcount2+1):
                    if  label_list_result2[i-1] == 0:
                        lb_Result_img2[i-1].configure(image=ng_img)
                    elif label_list_result2[i-1] == 1:
                        lb_Result_img2[i-1].configure(image=ok_img)
                popup.after(100, update_images)
        update_images()


def pointInitSet_Cam1(settype):
    if settype=="x":
        for i in range(1,pointcount+1):
            pts_x.append(100)
    elif settype=="y":
        for i in range(1,pointcount+1):
            pts_y.append(100)        
    elif settype=="a":
        for i in range(1,pointcount+1):
            pts_x.append(100)
            pts_y.append(100)
            pts_w.append(100)
            pts_h.append(100)

def pointInitSet_Cam2(settype):

    if settype=="x":
        for i in range(1,pointcount+1):
            pts_x2.append(100)
    elif settype=="y":
        for i in range(1,pointcount+1):
            pts_y2.append(100)        
    elif settype=="a":
        for i in range(1,pointcount+1):
            pts_x2.append(100)
            pts_y2.append(100)
            pts_w2.append(100)
            pts_h2.append(100)
if __name__ == '__main__':

   
     if os.path.isfile('./pointcnt.pickle') == True:
        with open('./pointcnt.pickle', 'rb') as f:    #point count load
            pointcount = int(pickle.load(f))
            print(pointcount)
     else:
        pointcount = 5

     if os.path.isfile('./pointcnt2.pickle') == True:
        with open('./pointcnt2.pickle', 'rb') as f:    #point count load
            pointcount2 = int(pickle.load(f))
            print(pointcount2)
     else:
        pointcount2 = 5

     root=tk.Tk()
     root.title("VISION")

     Tab_set1=ttk.Notebook(root, width=300, height=150)
     Tab_set1.grid(column=1, row=1, padx=0, pady=0)

     Tab_set1_1=ttk.Notebook(root, width=300, height=150)
     Tab_set1_1.grid(column=1, row=2, padx=0, pady=0)


     Tab_set2=ttk.Notebook(root, width=300, height=50)
     Tab_set2.grid(column=1, row=0, padx=0, pady=0)
   
     Tab_Image=ttk.Notebook(root, width=450, height=400)
     Tab_Image.grid(column=0, row=0,rowspan=3, padx=0, pady=0)

     #result


     frame_result1 = tk.LabelFrame(root,text="Result")
     frame_result1.grid(column=1, row=0, padx=0, pady=0)

     btn_resultView = tk.Button(frame_result1, text="Result Popup", command=popup)
     btn_resultView.grid(row=1, column=1)


     Tab_set2.add(frame_result1, text="result")

     #Setting
     frame_result2 = tk.LabelFrame(root,text="Setting")
     frame_result2.grid(column=1, row=0, padx=0, pady=0)

     txt_Set_Pts = tk.StringVar()
     txt_Set_Pt = ttk.Entry(frame_result2,textvariable=txt_Set_Pts,width=4)
     txt_Set_Pts.set(int(pointcount))    
     txt_Set_Pt.grid(row=1, column=1,columnspan=2)

     btn_set = tk.Button(frame_result2, text="CAM1 SET",command = lambda:[btn_pt_set(btn_pt_set,"btn_pt_set")])
     btn_set.grid(row=1, column=3,columnspan=2)
     Tab_set2.add(frame_result2, text="setting")


     txt_Set_Pts2 = tk.StringVar()
     txt_Set_Pt2 = ttk.Entry(frame_result2,textvariable=txt_Set_Pts2,width=4)
     txt_Set_Pts2.set(int(pointcount2))    
     txt_Set_Pt2.grid(row=1, column=5,columnspan=2)

     btn_set2 = tk.Button(frame_result2, text="CAM2 SET",command = lambda:[btn_pt_set(btn_pt_set,"btn_pt_set2")])
     btn_set2.grid(row=1, column=7,columnspan=2)

     
     btn_col_set = tk.Button(frame_result2, text="GETCOLOR",command = lambda:[Getcol_set(Getcol_set,"Getcol_set")])
     btn_col_set.grid(row=2, column=2)
     Tab_set2.add(frame_result2, text="GetColor")

     #popup
     btn_Auth = tk.Button(frame_result1, text="AUTH", command=popup_Auth)
     btn_Auth.grid(row=1, column=6)

     btn_ModelChange = tk.Button(frame_result1, text="Model Change", command=popup_ModelChage)
     btn_ModelChange.grid(row=1, column=4)

     # second camera1 widget setting
     for i in range(1,pointcount+1):
         pts_panel.append(tk.LabelFrame(root,text=f"CAM1 No{i} Setting",padx=5,pady=5))
         
         pts_panel[i-1].grid(column=1, row=0, padx=20, pady=20)
         
         Tab_set1.add(pts_panel[i-1], text=f"{i}")
         
         pts_w.append(0)
         pts_h.append(0)

       
         resultPt.append(0)
         chkval = tk.IntVar(value=0)
         chk_captureVar.append(chkval)
         chk_capture.append(tk.Checkbutton(pts_panel[i-1], text="CAPTURE",variable =chk_captureVar[i-1] ))
         btn_filemovegood.append(tk.Button(pts_panel[i-1], text="GOOD", width=4, height=0,command = lambda i=i: btn_git_upndown("up")))
         btn_filemovebad.append(tk.Button(pts_panel[i-1], text="BAD", width=4, height=0,command = lambda i=i: btn_git_upndown("down")))
         btn_filemoveinit.append(tk.Button(pts_panel[i-1], text="INIT", width=4, height=0,command = lambda i=i: btn_file_move(btn_file_move,"init",1,i)))
         

         pts_sx.append(tk.Scale( pts_panel[i-1], from_ = 0, to = w_max, orient = "horizontal",command = lambda value,i=i: pointSetting(i,"x",value,f"pt{i}_x")))
         pts_sy.append(tk.Scale( pts_panel[i-1], from_ = 0, to = w_max  , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"y",value,f"pt{i}_y")))
         pts_sw.append(tk.Scale( pts_panel[i-1], from_ = 0, to = 100   , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"w",value,f"pt{i}_w")))
         pts_sh.append(tk.Scale( pts_panel[i-1], from_ = 0, to = 100   , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"h",value,f"pt{i}_h")))
       
         chk_capture[i-1].grid(row=1, column=2)
         btn_filemovegood[i-1].grid(row=1, column=3)
         btn_filemovebad[i-1].grid(row=1, column=4)
         btn_filemoveinit[i-1].grid(row=1, column=5)

         pts_sx[i-1].grid(row=2, column=0, rowspan=2,columnspan=4)
         pts_sy[i-1].grid(row=4, column=0, rowspan=2,columnspan=4)
         pts_sw[i-1].grid(row=2, column=4, rowspan=2,columnspan=4)
         pts_sh[i-1].grid(row=4, column=4, rowspan=2,columnspan=4)

         points_std.append(np.ones(5))
         points_roi_std.append(0)


     # second camera2 widget setting
     for i in range(1,pointcount2+1):
         resultPt2.append(0)
         
         pts_panel2.append(tk.LabelFrame(root,text=f"CAM2 No{i} Setting",padx=5,pady=5))
         
         pts_panel2[i-1].grid(column=1, row=0, padx=20, pady=20)
         
         Tab_set1_1.add(pts_panel2[i-1], text=f"{i}")

         pts_w2.append(0)
         pts_h2.append(0)

         chkval2 = tk.IntVar(value=0)
         chk_captureVar2.append(chkval2)
         chk_capture2.append(tk.Checkbutton(pts_panel2[i-1], text="CAPTURE",variable =chk_captureVar2[i-1] ))
         btn_filemovegood2.append(tk.Button(pts_panel2[i-1], text="GOOD", width=4, height=0,command = lambda i=i: Range_popup(i,"CAM2")))
         btn_filemovebad2.append(tk.Button(pts_panel2[i-1], text="BAD", width=4, height=0,command = lambda i=i: Range_popup(i,"CAM2")))
         btn_filemoveinit2.append(tk.Button(pts_panel2[i-1], text="INIT", width=4, height=0,command = lambda i=i: btn_file_move(btn_file_move,"init",2,i)))

         chk_capture2[i-1].grid(row=1, column=2)
         btn_filemovegood2[i-1].grid(row=1, column=3)
         btn_filemovebad2[i-1].grid(row=1, column=4)
         btn_filemoveinit2[i-1].grid(row=1, column=5)

         pts_sx2.append(tk.Scale( pts_panel2[i-1], from_ = 0, to = w_max, orient = "horizontal",command = lambda value,i=i: pointSetting(i,"x2",value,f"pt{i}_x2")))
         pts_sy2.append(tk.Scale( pts_panel2[i-1], from_ = 0, to = w_max  , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"y2",value,f"pt{i}_y2")))
         pts_sw2.append(tk.Scale( pts_panel2[i-1], from_ = 0, to = 100   , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"w2",value,f"pt{i}_w2")))
         pts_sh2.append(tk.Scale( pts_panel2[i-1], from_ = 0, to = 100   , orient = "horizontal",command = lambda value,i=i: pointSetting(i,"h2",value,f"pt{i}_h2")))
       
         pts_sx2[i-1].grid(row=2, column=0, rowspan=2,columnspan=4)
         pts_sy2[i-1].grid(row=4, column=0, rowspan=2,columnspan=4)
         pts_sw2[i-1].grid(row=2, column=4, rowspan=2,columnspan=4)
         pts_sh2[i-1].grid(row=4, column=4, rowspan=2,columnspan=4)

                 
         points_std2.append(np.ones(5))
         points_roi_std2.append(0)
         
         
     # SET FILE
     isfile = path.exists('./ptsx.pickle')

     if isfile == True:
         #pts
         if os.path.getsize('./ptsx.pickle') > 0:
            with open('./ptsx.pickle', 'rb') as f:  
                pts_x = pickle.load(f)
                if (len(pts_x) == 0):
                    pointInitSet_Cam1("x")
                if (pointcount - len(pts_x)) > 0:
                    for i in range(1,pointcount - len(pts_x)+1):
                        pts_x.append(100)
                    
                for i in range(1,pointcount+1):
                    if pts_x[i-1] <- 0:
                        pts_x[i-1] =10
             
                if len(pts_x) < pointcount:
                    for i in range(len(pts_x),pointcount):
                        pts_x.append(10)
                print("*****X-Bar Setting *****")
                print(pts_x)
     else:
         for i in range(1,pointcount+1):
             pts_x[i-1] =10
                 

     isfile = path.exists('./ptsy.pickle')

     if isfile == True:
         if os.path.getsize('./ptsy.pickle') > 0:
            with open('./ptsy.pickle', 'rb') as f:  
                pts_y = pickle.load(f)
                if (len(pts_y) == 0):
                    pointInitSet_Cam1("y")
                if (pointcount - len(pts_y)) > 0:
                    for i in range(1,pointcount - len(pts_y)+1):
                        pts_y.append(100)

                for i in range(1,pointcount+1):
                     if pts_y[i-1] <- 0:
                         pts_y[i-1] =10
					
                if len(pts_y) < pointcount:
                     for i in range(len(pts_y),pointcount):
                         pts_y.append(0)
                print("*****Y-Bar Setting *****")
                print(pts_y)
     else:
         for i in range(1,pointcount+1):
             pts_y[i-1] =10
     
     isfile = path.exists('./ptsw.pickle')

     if isfile == True:            
         if os.path.getsize('./ptsw.pickle') > 0:
            with open('./ptsw.pickle', 'rb') as f:  
                pts_w = pickle.load(f)
                if (len(pts_w) == 0):
                    pointInitSet_Cam1("w")
                if (pointcount - len(pts_w)) > 0:
                    for i in range(1,pointcount - len(pts_w)+1):
                        pts_w.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_w[i-1] <- 0:
                        pts_w[i-1] =10
             
                if len(pts_w) < pointcount:
                    for i in range(len(pts_w),pointcount):
                        pts_w.append(10)
                print("*****w-Bar Setting *****")
                print(pts_w)
     else:
         for i in range(1,pointcount+1):
             pts_w[i-1] =10

     isfile = path.exists('./ptsh.pickle')

     if isfile == True:            

         if os.path.getsize('./ptsh.pickle') > 0:
            with open('./ptsh.pickle', 'rb') as f:  
                pts_h = pickle.load(f)
                if (len(pts_h) == 0):
                    pointInitSet_Cam1("h")
                if (pointcount - len(pts_h)) > 0:
                    for i in range(1,pointcount - len(pts_h)+1):
                        pts_h.append(100)

                for i in range(1,pointcount+1):
                     if pts_h[i-1] <- 0:
                         pts_h[i-1] =10
					
                if len(pts_h) < pointcount:
                     for i in range(len(pts_h),pointcount):
                         pts_h.append(0)
                print("*****h-Bar Setting *****")
                print(pts_h)
     else:
         for i in range(1,pointcount+1):
             pts_h[i-1] =10
         
     #cam2 point file
     isfile = path.exists('./ptsx2.pickle')

     if isfile == True:
         #pts
         if os.path.getsize('./ptsx2.pickle') > 0:
            with open('./ptsx2.pickle', 'rb') as f:  
                pts_x2 = pickle.load(f)
                if (len(pts_x2) == 0):
                    pointInitSet_Cam2("x")
                if (pointcount - len(pts_x2)) > 0:
                    for i in range(1,pointcount - len(pts_x2)+1):
                        pts_x2.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_x2[i-1] <- 0:
                        pts_x2[i-1] =10
             
                if len(pts_x2) < pointcount:
                    for i in range(len(pts_x2),pointcount):
                        pts_x2.append(10)
                print("*****X2-Bar Setting *****")
                print(pts_x2)
     else:
         for i in range(1,pointcount+1):
             pts_x2[i-1] =10

     isfile = path.exists('./ptsy2.pickle')

     if isfile == True:
         if os.path.getsize('./ptsy2.pickle') > 0:
            with open('./ptsy2.pickle', 'rb') as f:  
                pts_y2 = pickle.load(f)
                if (len(pts_y2) == 0):
                    pointInitSet_Cam2("y")
                if (pointcount - len(pts_y2)) > 0:
                    for i in range(1,pointcount - len(pts_y2)+1):
                        pts_y2.append(100)
                for i in range(1,pointcount+1):
                     if pts_y2[i-1] <- 0:
                         pts_y2[i-1] =10
					
                if len(pts_y2) < pointcount:
                     for i in range(len(pts_y2),pointcount):
                         pts_y2.append(0)
                print("*****Y2-Bar Setting *****")
                print(pts_y2)
     else:
         for i in range(1,pointcount+1):
             pts_y2[i-1] =10

     isfile = path.exists('./ptsw2.pickle')

     if isfile == True:
         if os.path.getsize('./ptsw2.pickle') > 0:
            with open('./ptsw2.pickle', 'rb') as f:  
                pts_w2 = pickle.load(f)
                if (len(pts_w2) == 0):
                    pointInitSet_Cam2("w")
                if (pointcount - len(pts_w2)) > 0:
                    for i in range(1,pointcount2 - len(pts_w2)+1):
                        pts_w2.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts_w2[i-1] <- 0:
                        pts_w2[i-1] =10
             
                if len(pts_w2) < pointcount:
                    for i in range(len(pts_w2),pointcount2):
                        pts_w2.append(10)
                print("*****W2-Bar Setting *****")
                print(pts_w2)
     else:
         for i in range(1,pointcount+1):
             pts_w2[i-1] =10

     isfile = path.exists('./ptsh2.pickle')

     if isfile == True:
         if os.path.getsize('./ptsh2.pickle') > 0:
            with open('./ptsh2.pickle', 'rb') as f:  
                pts_h2 = pickle.load(f)
                if (len(pts_h2) == 0):
                    pointInitSet_Cam2("h")
                if (pointcount - len(pts_h2)) > 0:
                    for i in range(1,pointcount - len(pts_h2)+1):
                        pts_h2.append(100)

                for i in range(1,pointcount+1):
                     if pts_h2[i-1] <- 0:
                         pts_h2[i-1] =10
					
                if len(pts_h2) < pointcount:
                     for i in range(len(pts_h2),pointcount):
                         pts_h2.append(0)
                print("*****H2-Bar Setting *****")
                print(pts_h2)
           
     else:
         for i in range(1,pointcount+1):
             pts_h2[i-1] =10
             
     isfile = path.exists('./points_std.pickle')

     if isfile == True:
         with open('points_std.pickle', 'rb') as f:
             points_std = pickle.load(f)

             print("*****point STANDART setting*****")
           
             for i in range(len(points_std),pointcount):
                     points_std.append(np.ones(5))

             if len(points_std) < pointcount:
                 for i in range(len(points_std),pointcount):
                     points_std[i-1] = np.append(points_std[i-1],10)


             
             for i in range(1,pointcount+1):
                 btn_Pointdis[i-1].config(text=str(np.median(points_std[i-1])))

             print(points_std)
     else:
         for i in range(1,pointcount+1):
             points_std[i-1] = np.append(points_std[i-1],10)
             print(points_std[i-1])

     isfile = path.exists('./points_std2.pickle')

     if isfile == True:
         with open('points_std2.pickle', 'rb') as f:
             points_std2 = pickle.load(f)

             print("*****point2 STANDART setting*****")
           
             for i in range(len(points_std2),pointcount2):
                     points_std2.append(np.ones(5))

             if len(points_std2) < pointcount2:
                 for i in range(len(points_std2),pointcount2):
                     points_std2[i-1] = np.append(points_std2[i-1],10)


             
             for i in range(1,pointcount2+1):
                 btn_Pointdis2[i-1].config(text=str(np.median(points_std2[i-1])))
             
     else:
         for i in range(1,pointcount2+1):
             points_std2[i-1] = np.append(points_std2[i-1],10)
             print(points_std2[i-1])


     if isfile == True:
         #pts_rrl
         if os.path.getsize('./pts_rrl.pickle') > 0:
            with open('./pts_rrl.pickle', 'rb') as f:  
                pts_rrl = pickle.load(f)
                if (len(pts_rrl) == 0):
                    for i in range(1,pointcount+1):
                        pts_rrl.append(100)
                if (pointcount - len(pts_rrl)) > 0:
                    for i in range(1,pointcount - len(pts_rrl)+1):
                        pts_rrl.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rrl[i-1] <- 0:
                        pts_rrl[i-1] =10
             
                if len(pts_rrl) < pointcount:
                    for i in range(len(pts_rrl),pointcount):
                        pts_rrl.append(10)
                print("*****pts_rrl-Bar Setting *****")
                print(pts_rrl)
     else:
         for i in range(1,pointcount+1):
             pts_rrl.append(100)

     if isfile == True:
         #pts_rrh
         if os.path.getsize('./pts_rrh.pickle') > 0:
            with open('./pts_rrh.pickle', 'rb') as f:  
                pts_rrh = pickle.load(f)
                if (len(pts_rrh) == 0):
                    for i in range(1,pointcount+1):
                        pts_rrh.append(100)
                if (pointcount - len(pts_rrh)) > 0:
                    for i in range(1,pointcount - len(pts_rrh)+1):
                        pts_rrh.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rrh[i-1] <- 0:
                        pts_rrh[i-1] =10
             
                if len(pts_rrh) < pointcount:
                    for i in range(len(pts_rrh),pointcount):
                        pts_rrh.append(10)
                print("*****pts_rrh-Bar Setting *****")
                print(pts_rrh)
     else:
         for i in range(1,pointcount+1):
             pts_rrh.append(100)

     if isfile == True:
         #pts_rgl
         if os.path.getsize('./pts_rgl.pickle') > 0:
            with open('./pts_rgl.pickle', 'rb') as f:  
                pts_rgl = pickle.load(f)
                if (len(pts_rgl) == 0):
                    for i in range(1,pointcount+1):
                        pts_rgl.append(100)
                if (pointcount - len(pts_rgl)) > 0:
                    for i in range(1,pointcount - len(pts_rgl)+1):
                        pts_rgl.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rgl[i-1] <- 0:
                        pts_rgl[i-1] =10
             
                if len(pts_rgl) < pointcount:
                    for i in range(len(pts_rgl),pointcount):
                        pts_rgl.append(10)
                print("*****pts_rgl-Bar Setting *****")
                print(pts_rgl)
     else:
         for i in range(1,pointcount+1):
             pts_rgl.append(100)

     if isfile == True:
         #pts_rgh
         if os.path.getsize('./pts_rgh.pickle') > 0:
            with open('./pts_rgh.pickle', 'rb') as f:  
                pts_rgh = pickle.load(f)
                if (len(pts_rgh) == 0):
                    for i in range(1,pointcount+1):
                        pts_rgh.append(100)
                if (pointcount - len(pts_rgh)) > 0:
                    for i in range(1,pointcount - len(pts_rgh)+1):
                        pts_rgh.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rgh[i-1] <- 0:
                        pts_rgh[i-1] =10
             
                if len(pts_rgh) < pointcount:
                    for i in range(len(pts_rgh),pointcount):
                        pts_rgh.append(10)
                print("*****pts_rgh-Bar Setting *****")
                print(pts_rgh)
     else:
         for i in range(1,pointcount+1):
             pts_rgh.append(100)
     
     if isfile == True:
         #pts_rbl
         if os.path.getsize('./pts_rbl.pickle') > 0:
            with open('./pts_rbl.pickle', 'rb') as f:  
                pts_rbl = pickle.load(f)
                if (len(pts_rbl) == 0):
                    for i in range(1,pointcount+1):
                        pts_rbl.append(100)
                if (pointcount - len(pts_rbl)) > 0:
                    for i in range(1,pointcount - len(pts_rbl)+1):
                        pts_rbl.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rbl[i-1] <- 0:
                        pts_rbl[i-1] =10
             
                if len(pts_rbl) < pointcount:
                    for i in range(len(pts_rbl),pointcount):
                        pts_rbl.append(10)
                print("*****pts_rbl-Bar Setting *****")
                print(pts_rbl)
     else:
         for i in range(1,pointcount+1):
             pts_rbl.append(100)

     if isfile == True:
         #pts_rbh
         if os.path.getsize('./pts_rbh.pickle') > 0:
            with open('./pts_rbh.pickle', 'rb') as f:  
                pts_rbh = pickle.load(f)
                if (len(pts_rbh) == 0):
                    for i in range(1,pointcount+1):
                        pts_rbh.append(100)
                if (pointcount - len(pts_rbh)) > 0:
                    for i in range(1,pointcount - len(pts_rbh)+1):
                        pts_rbh.append(100)
               
                for i in range(1,pointcount+1):
                    if pts_rbh[i-1] <- 0:
                        pts_rbh[i-1] =10
             
                if len(pts_rbh) < pointcount:
                    for i in range(len(pts_rbh),pointcount):
                        pts_rbh.append(10)
                print("*****pts_rbh-Bar Setting *****")
                print(pts_rbh)
     else:
         for i in range(1,pointcount+1):
             pts_rbh.append(100)

     if isfile == True:
         #pts2_rrl
         if os.path.getsize('./pts2_rrl.pickle') > 0:
            with open('./pts2_rrl.pickle', 'rb') as f:  
                pts2_rrl = pickle.load(f)
                if (len(pts2_rrl) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rrl.append(100)
                if (pointcount2 - len(pts2_rrl)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rrl)+1):
                        pts2_rrl.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rrl[i-1] <- 0:
                        pts2_rrl[i-1] =10
             
                if len(pts2_rrl) < pointcount2:
                    for i in range(len(pts2_rrl),pointcount2):
                        pts2_rrl.append(10)
                print("*****pts2_rrl-Bar Setting *****")
                print(pts2_rrl)
     else:
         for i in range(1,pointcount2+1):
             pts2_rrl.append(100)

     if isfile == True:
         #pts2_rrh
         if os.path.getsize('./pts2_rrh.pickle') > 0:
            with open('./pts2_rrh.pickle', 'rb') as f:  
                pts2_rrh = pickle.load(f)
                if (len(pts2_rrh) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rrh.append(100)
                if (pointcount2 - len(pts2_rrh)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rrh)+1):
                        pts2_rrh.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rrh[i-1] <- 0:
                        pts2_rrh[i-1] =10
             
                if len(pts2_rrh) < pointcount2:
                    for i in range(len(pts2_rrh),pointcount2):
                        pts2_rrh.append(10)
                print("*****pts2_rrh-Bar Setting *****")
                print(pts2_rrh)
     else:
         for i in range(1,pointcount2+1):
             pts2_rrh.append(100)

     if isfile == True:
         #pts2_rgl
         if os.path.getsize('./pts2_rgl.pickle') > 0:
            with open('./pts2_rgl.pickle', 'rb') as f:  
                pts2_rgl = pickle.load(f)
                if (len(pts2_rgl) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rgl.append(100)
                if (pointcount2 - len(pts2_rgl)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rgl)+1):
                        pts2_rgl.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rgl[i-1] <- 0:
                        pts2_rgl[i-1] =10
             
                if len(pts2_rgl) < pointcount2:
                    for i in range(len(pts2_rgl),pointcount2):
                        pts2_rgl.append(10)
                print("*****pts2_rgl-Bar Setting *****")
                print(pts2_rgl)
     else:
         for i in range(1,pointcount2+1):
             pts2_rgl.append(100)

     if isfile == True:
         #pts2_rgh
         if os.path.getsize('./pts2_rgh.pickle') > 0:
            with open('./pts2_rgh.pickle', 'rb') as f:  
                pts2_rgh = pickle.load(f)
                if (len(pts2_rgh) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rgh.append(100)
                if (pointcount2 - len(pts2_rgh)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rgh)+1):
                        pts2_rgh.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rgh[i-1] <- 0:
                        pts2_rgh[i-1] =10
             
                if len(pts2_rgh) < pointcount2:
                    for i in range(len(pts2_rgh),pointcount2):
                        pts2_rgh.append(10)
                print("*****pts2_rgh-Bar Setting *****")
                print(pts2_rgh)
     else:
         for i in range(1,pointcount2+1):
             pts2_rgh.append(100)
     
     if isfile == True:
         #pts2_rbl
         if os.path.getsize('./pts2_rbl.pickle') > 0:
            with open('./pts2_rbl.pickle', 'rb') as f:  
                pts2_rbl = pickle.load(f)
                if (len(pts2_rbl) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rbl.append(100)
                if (pointcount2 - len(pts2_rbl)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rbl)+1):
                        pts2_rbl.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rbl[i-1] <- 0:
                        pts2_rbl[i-1] =10
             
                if len(pts2_rbl) < pointcount2:
                    for i in range(len(pts2_rbl),pointcount2):
                        pts2_rbl.append(10)
                print("*****pts2_rbl-Bar Setting *****")
                print(pts2_rbl)
     else:
         for i in range(1,pointcount2+1):
             pts2_rbl.append(100)

     if isfile == True:
         #pts2_rbh
         if os.path.getsize('./pts2_rbh.pickle') > 0:
            with open('./pts2_rbh.pickle', 'rb') as f:  
                pts2_rbh = pickle.load(f)
                if (len(pts2_rbh) == 0):
                    for i in range(1,pointcount2+1):
                        pts2_rbh.append(100)
                if (pointcount2 - len(pts2_rbh)) > 0:
                    for i in range(1,pointcount2 - len(pts2_rbh)+1):
                        pts2_rbh.append(100)
               
                for i in range(1,pointcount2+1):
                    if pts2_rbh[i-1] <- 0:
                        pts2_rbh[i-1] =10
             
                if len(pts2_rbh) < pointcount2:
                    for i in range(len(pts2_rbh),pointcount2):
                        pts2_rbh.append(10)
                print("*****pts2_rbh-Bar Setting *****")
                print(pts2_rbh)
     else:
         for i in range(1,pointcount2+1):
             pts2_rbh.append(100)

     if authConfirm:
        set_authConfirm_color("green")
     else:
        set_authConfirm_color("red")

     thread_img = threading.Thread(target = camThread,args=())
     thread_img.daemon = True
     thread_img.start()

     thread_img2 = threading.Thread(target = cam2Thread,args=())
     thread_img2.daemon = True
     thread_img2.start()
   
     root.mainloop()

