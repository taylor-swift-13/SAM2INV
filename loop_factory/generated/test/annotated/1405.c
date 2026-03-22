int main1(){
  int u, ij, x5;
  u=(1%10)+5;
  ij=0;
  x5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ij == 4 * x5;
  loop invariant x5 <= u;
  loop invariant 0 <= x5;
  loop assigns x5, ij;
*/
while (x5<u) {
      x5 += 1;
      ij++;
      ij = ij + 3;
  }
}