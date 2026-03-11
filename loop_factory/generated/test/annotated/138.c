int main1(){
  int t, i, u5, oc;
  t=1*3;
  i=t;
  u5=-3;
  oc=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ( (i == t && u5 == -3) || (i == 0 && u5 == -3 + oc) );
  loop invariant t == 3;
  loop invariant oc == -6;
  loop assigns u5, i;
*/
while (i>0) {
      if (!(!(i<t/2))) {
          u5 += 1;
      }
      else {
          u5 += oc;
      }
      i = 0;
  }
}