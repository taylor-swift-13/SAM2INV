int main1(){
  int l, sbrt, vf, tv, gs0;
  l=80;
  sbrt=4;
  vf=(1%40)+2;
  tv=0;
  gs0=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((gs0 - 5) % sbrt == 0);
  loop invariant gs0 >= 5;
  loop invariant (gs0 - 5) % 4 == 0;
  loop invariant l == 80;
  loop invariant vf > 0;
  loop invariant tv >= 0;
  loop assigns gs0, tv, vf;
*/
while (vf!=tv) {
      tv = vf;
      vf = (vf+l/vf)/2;
      gs0 = gs0 + sbrt;
  }
}