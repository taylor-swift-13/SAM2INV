int main1(){
  int vf, cg, c5o, ac, m;
  vf=1;
  cg=0;
  c5o=0;
  ac=0;
  m=cg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ac == c5o*(c5o - 1)/2;
  loop invariant m == c5o*(c5o - 1)*(c5o + 1)/6;
  loop invariant 0 <= c5o;
  loop invariant c5o <= vf;
  loop assigns ac, m, c5o;
*/
while (c5o<vf) {
      ac = ac + c5o;
      m += ac;
      c5o += 1;
  }
}