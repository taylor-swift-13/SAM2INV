int main1(int y){
  int f, ggpc, aw, zpme, sl6;
  f=y;
  ggpc=0;
  aw=ggpc;
  zpme=ggpc;
  sl6=ggpc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == y;
  loop invariant aw == 0;
  loop invariant 3*ggpc == 2*sl6;
  loop invariant ggpc >= 0;
  loop invariant f == \at(y, Pre);
  loop invariant 3*zpme == 2*sl6;
  loop assigns ggpc, aw, sl6, zpme;
*/
while (ggpc < f) {
      ggpc = ggpc + 1 + (ggpc < y);
      aw = aw*3;
      sl6 = sl6 + 3;
      zpme += 2;
  }
}