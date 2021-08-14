# Numpy, Tensorflow などのインポート
import numpy as np 
import scipy as sp
import sklearn as sk
import matplotlib as mpl 
import matplotlib.pylab as plt
import tensorflow as tf
import keras

# Keras のインポート
from keras.layers import Input
from keras.layers import Dense
from keras.models import Model
from keras.datasets import mnist
from tensorflow.keras.utils import to_categorical
from keras.layers import Conv2D, MaxPooling2D, Flatten, Dropout, BatchNormalization

# 畳み込みニューラルネットワーク
B_inputs = Input(shape=(8,8,2), name="Input")
B_middle1 = Flatten(name="Level_1")(B_inputs)
B_middle2 = Dense(300, activation='tanh', name="Level_2")(B_middle1)
B_middle3 = Dropout(0.03, name="Level_3")(B_middle2)
B_middle4 = Dense(100, activation='tanh', name="Level_4")(B_middle3)
B_outputs = Dense(2, activation='softmax', name="Level_5")(B_middle4)

# コンパイル
model_V = keras.Model(inputs=B_inputs, outputs=B_outputs, name="OthelloAI_V") #入力と出力だけ指定すればOK
model_V.summary()

# データの読み込み
import numpy as np
datas = 614595
x_train = np.loadtxt('output1.csv', delimiter=',', dtype='float32')
y_train = np.loadtxt('output2.csv', delimiter=',', dtype='float32')
x_train = x_train.reshape(datas, 8, 8, 2)
y_train = y_train.reshape(datas, 2)
model_V.compile(
    loss=keras.losses.CategoricalCrossentropy(), #ここでクロスエントロピーを指定
    optimizer=keras.optimizers.Adam(), #学習アルゴリズムにAdamを指定
    metrics=["accuracy"], #性能評価にaccuracyを指定
)

#学習前
param_initial = model_V.get_weights()

#学習スタート
epochs = 25 #エポック数（全データを概ねチェックして更新する回数）を指定
history = model_V.fit(x_train, y_train, batch_size=100, epochs=epochs, verbose=1, validation_split=0.2)

# 出力
param_learn = model_V.get_weights()
with open('record.txt', 'w') as f:
  for i in range(len(param_learn[0])):
    print(param_learn[0][i], file=f)
  print(param_learn[1], file=f)
  for i in range(len(param_learn[2])):
    print(param_learn[2][i], file=f)
  print(param_learn[3], file=f)
  for i in range(len(param_learn[4])):
    print(param_learn[4][i], file=f)
  print(param_learn[5], file=f)