int main1(int v,int s){
  int j7, vq, u1, x5, tas, ln, wp1;

  j7=v+16;
  vq=3;
  u1=6;
  x5=6;
  tas=0;
  ln=7;
  wp1=0;

  while (vq<j7) {
      if (!(!(vq%3==0))) {
          if (u1>0) {
              u1 -= 1;
              tas++;
          }
      }
      else {
          if (u1<ln) {
              u1++;
              x5 += 1;
          }
      }
      wp1++;
      vq = vq + 1;
  }

}
