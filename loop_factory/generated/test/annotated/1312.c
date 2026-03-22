int main1(){
  int nnj, c, h;
  nnj=0;
  c=(1%28)+10;
  h=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 11 - nnj*(nnj - 1)/2;
  loop invariant (nnj == 0) ==> (h == -4);
  loop invariant (nnj > 0) ==> (h % 3 == 0);
  loop invariant nnj >= 0;
  loop invariant 0 <= nnj <= 5;
  loop assigns c, h, nnj;
*/
while (1) {
      if (!(c>nnj)) {
          break;
      }
      c -= nnj;
      h = h + c;
      nnj += 1;
      h = h*3;
  }
}