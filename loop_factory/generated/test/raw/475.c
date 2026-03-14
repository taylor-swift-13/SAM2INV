int main1(){
  int me, u, dh1, w, y6;

  me=1+24;
  u=me;
  dh1=(1%18)+5;
  w=(1%15)+3;
  y6=dh1;

  while (dh1!=0) {
      w = w - 1;
      dh1 -= 1;
      y6 = y6 + u;
  }

  while (w+1<=dh1) {
      u = u+me*w;
      dh1 = ((w+1))+(-(1));
  }

}
