int main1(int c,int q){
  int y4, dd5f, nlu, yj;
  y4=q-7;
  dd5f=y4;
  nlu=16;
  yj=dd5f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yj >= dd5f;
  loop invariant dd5f <= y4;
  loop invariant nlu == 16;
  loop invariant y4 == q - 7;
  loop invariant dd5f <= \at(q, Pre) - 7;
  loop invariant yj >= \at(q, Pre) - 7;
  loop assigns yj, dd5f;
*/
for (; dd5f>=1; dd5f -= 1) {
      yj = yj*yj+nlu;
  }
}