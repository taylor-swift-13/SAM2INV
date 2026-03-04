int main1(){
  int x7u, ql, shfl;
  x7u=1;
  ql=x7u;
  shfl=ql;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x7u == 1;
  loop invariant ql <= x7u;
  loop invariant shfl >= ql;
  loop invariant shfl >= 0;
  loop invariant ql >= 1;
  loop invariant shfl >= 6*(ql - 1) + 1;
  loop invariant shfl >= 1;
  loop invariant ql >= 0;
  loop assigns ql, shfl;
*/
while (1) {
      if (!(ql<x7u)) {
          break;
      }
      shfl = shfl + 3;
      ql += 1;
      shfl = shfl + shfl;
  }
}