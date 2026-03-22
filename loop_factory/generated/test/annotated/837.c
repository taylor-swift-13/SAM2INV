int main1(){
  int ota, l, qch, hv, vr;
  ota=60;
  l=ota;
  qch=1;
  hv=0;
  vr=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l >= 60;
  loop invariant qch >= 1;
  loop invariant vr >= 3;
  loop invariant 0 <= hv <= ota;
  loop assigns hv, l, qch, vr;
*/
while (1) {
      if (hv>=ota) {
          break;
      }
      hv = hv + 1;
      l = l*vr+1;
      qch = qch*vr;
      vr += l;
  }
}