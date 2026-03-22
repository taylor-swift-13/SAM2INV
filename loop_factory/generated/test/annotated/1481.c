int main1(int o){
  int ab0l, c, rqx;
  ab0l=0;
  c=(o%20)+10;
  rqx=(o%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ab0l + c + rqx == (\at(o,Pre) % 20) + (\at(o,Pre) % 15) + 18;
  loop invariant 0 <= ab0l;
  loop invariant c + rqx + ab0l == (o % 20) + 10 + (o % 15) + 8;
  loop assigns ab0l, c, rqx;
*/
for (; c>0&&rqx>0; ab0l = ab0l + 1) {
      if (!(!(ab0l%2==0))) {
          c--;
      }
      else {
          rqx = rqx - 1;
      }
  }
}