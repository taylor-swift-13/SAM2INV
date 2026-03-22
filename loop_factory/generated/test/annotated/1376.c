int main1(int r){
  int kq, n0di;
  kq=67;
  n0di=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kq == 67;
  loop invariant (n0di == 1) || (n0di == 3) || (n0di == 9) || (n0di == 27);
  loop invariant r == \at(r, Pre);
  loop assigns n0di;
*/
for (; n0di*3<=kq; n0di = n0di*3) {
  }
}