int main1(){
  int af, v, i, fv;
  af=76;
  v=af;
  i=af;
  fv=af;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i - fv * v == -5700;
  loop invariant af == 76;
  loop invariant fv == 76;
  loop invariant v >= af;
  loop assigns i, v;
*/
while (v-1>=0) {
      if (!(!(v<af/2))) {
          i = i + 1;
      }
      else {
          i += fv;
      }
      v++;
  }
}