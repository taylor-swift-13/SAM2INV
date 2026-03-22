int main1(){
  int yrf, w, i9l, ku, s, b7n, g0, rz;

  yrf=(1%16)+4;
  w=yrf;
  i9l=(1%20)+10;
  ku=(1%15)+8;
  s=4;
  b7n=yrf;
  g0=0;
  rz=w;

  while (i9l>0&&ku>0) {
      if (w%2==0) {
          i9l--;
      }
      else {
          ku = ku - 1;
      }
      w += 1;
      if ((w%9)==0) {
          s++;
      }
      b7n += i9l;
      s++;
      b7n = b7n + s;
      rz = rz + g0;
      g0++;
      if (w+3<=rz+yrf) {
          g0++;
      }
  }

}
