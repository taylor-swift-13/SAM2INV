int main1(){
  int w, v0, n1;
  w=0;
  v0=56;
  n1=28;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n1 + w == 28;
  loop invariant v0 == 28 + n1;
  loop invariant n1 >= 0;
  loop invariant w >= 0;
  loop assigns n1, v0, w;
*/
while (n1>0) {
      n1--;
      w += 1;
      v0 -= 1;
  }
}