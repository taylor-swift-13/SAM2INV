int main1(){
  int yva8, qf, s5, f;
  yva8=61;
  qf=0;
  s5=0;
  f=qf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == s5*(s5 + 1) / 2;
  loop invariant qf <= yva8;
  loop assigns f, qf, s5;
*/
while (qf<yva8) {
      s5 = s5 + 1;
      f += s5;
      qf = yva8;
  }
}