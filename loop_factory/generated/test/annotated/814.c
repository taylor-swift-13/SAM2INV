int main1(int z,int x){
  int i5, uq, w, du;
  i5=x+4;
  uq=0;
  w=z;
  du=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i5 == x + 4;
  loop invariant w == z;
  loop invariant du == 0 && (uq == 0 || uq == i5);
  loop assigns du, uq;
*/
while (uq<i5) {
      du = du+w*uq;
      uq = i5;
  }
}