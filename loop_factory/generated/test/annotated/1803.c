int main1(){
  int ms, j, du, ng, e2k;
  ms=10;
  j=0;
  du=j;
  ng=ms;
  e2k=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j <= ms;
  loop invariant e2k == 0;
  loop invariant ng >= 10;
  loop invariant du >= 0;
  loop invariant 2*du == j*ng;
  loop assigns du, j, ng, e2k;
*/
while (j < ms) {
      du = du*2 + ng;
      j++;
      ng = ng*2 + e2k;
      e2k = e2k*2;
  }
}