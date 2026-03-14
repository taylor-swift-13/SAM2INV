int main1(int w,int c){
  int qyc, ln, bl7, li, mm;

  qyc=c*4;
  ln=0;
  bl7=0;
  li=0;
  mm=qyc;

  while (bl7<=qyc-1) {
      li = bl7;
      w = w+qyc-ln;
      bl7 += 4;
  }

  while (bl7+8<=li) {
      w += 2;
      ln = ln+mm*bl7;
      li = (bl7+8)-1;
  }

}
