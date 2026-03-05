int main1(int t,int k){
  int oh, ek, f0l;
  oh=t;
  ek=0;
  f0l=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ek == 0;
  loop invariant f0l == 2 - ((t - \at(t,Pre)) % 2);
  loop invariant t >= \at(t,Pre);
  loop invariant k - \at(k,Pre) >= t - \at(t,Pre);
  loop invariant k - \at(k,Pre) <= 2*(t - \at(t,Pre));
  loop assigns k, t, f0l;
*/
while (ek<oh) {
      if (f0l==1) {
          f0l = 2;
      }
      else {
          if (f0l==2) {
              f0l = 1;
          }
      }
      k += f0l;
      t += 1;
  }
}