int main1(){
  int u6r, in, pn, pr1, f2;
  u6r=1;
  in=4;
  pn=0;
  pr1=1;
  f2=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pn == 0;
  loop invariant u6r == 1;
  loop invariant pr1 == 1;
  loop invariant f2 == in - 7;
  loop invariant f2 >= -3;
  loop assigns pn, pr1, f2, in;
*/
while (in<=u6r) {
      pn = pn*in;
      if (in<u6r) {
          pr1 = pr1*in;
      }
      f2 = f2 + pr1;
      in += 1;
  }
}