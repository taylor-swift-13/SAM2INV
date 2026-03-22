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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i9l >= 0;
  loop invariant ku >= 0;
  loop invariant w >= yrf;
  loop invariant b7n >= yrf;
  loop invariant s >= 4;
  loop invariant g0 >= 0;
  loop invariant (i9l + ku) <= 20;
  loop invariant w + i9l + ku == 25;
  loop invariant b7n >= 0;
  loop invariant rz >= 0;
  loop assigns i9l, ku, w, s, b7n, rz, g0;
*/
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