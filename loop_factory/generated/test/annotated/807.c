int main1(){
  int o7, t, ky, t0;
  o7=1;
  t=1;
  ky=0;
  t0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == o7;
  loop invariant ky == 0;
  loop invariant t0 == 0;
  loop assigns t0, t;
*/
while (1) {
      if (!(t<=o7-1)) {
          break;
      }
      t0 = t0+ky*t;
      t = o7;
  }
}