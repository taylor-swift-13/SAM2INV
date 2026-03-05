int main55(int i){
  int y, cx, s1, u4h, xb, fdj;

  y=i;
  cx=99;
  s1=0;
  u4h=i;
  xb=i;
  fdj=y;

  while (cx>0) {
      s1 += 4;
      cx -= 4;
      i = i + cx;
      u4h = u4h*2;
      fdj = fdj%6;
      xb = xb + u4h;
  }

}
