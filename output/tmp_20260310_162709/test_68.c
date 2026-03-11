int main1(){
  int q, cl, g;
  q=1;
  cl=0;
  g=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == 1;
  loop invariant cl + 2*g == 2*q;
  loop invariant 0 <= g <= q;
  loop invariant cl % 2 == 0;
  loop assigns cl, g;
*/
while (cl<q&&g>0) {
      g -= 1;
      cl = cl + 1;
      cl = cl+g+g;
      cl = cl + 1;
  }
/*@
  assert (q == 1) &&
         (g == 0) &&
         (cl == 2);
*/
}
