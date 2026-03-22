int main1(){
  int u7, qk1, m, hf, cj;
  u7=1;
  qk1=u7;
  m=1;
  hf=0;
  cj=qk1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cj == hf + 1;
  loop invariant cj == qk1 * (hf + 1);
  loop invariant cj == qk1 * m;
  loop invariant qk1 == u7;
  loop invariant hf == m - 1;
  loop invariant hf >= 0;
  loop assigns cj, m, hf;
*/
while (m<=u7) {
      cj = cj + qk1;
      m = 2*m;
      hf = (1)+(hf);
  }
}