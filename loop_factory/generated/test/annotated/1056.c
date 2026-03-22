int main1(){
  int vhk, el, ym, net, vq;
  vhk=1+8;
  el=vhk+4;
  ym=-5;
  net=4;
  vq=vhk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*net == 8 + el*(ym+5)*(ym-6);
  loop invariant el == 13;
  loop invariant (vhk == 0 || vhk == 9);
  loop invariant ym >= -5;
  loop assigns net, vq, ym, vhk;
*/
while (1) {
      if (!(el-vhk>0)) {
          break;
      }
      net = net+ym*el;
      vq = vq + net;
      ym += 1;
      vhk = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant net <= ym;
  loop assigns net, vq, vhk;
*/
while (net<=ym-1) {
      vhk = vhk + vq;
      vq = vq + net;
      net = ym;
  }
}