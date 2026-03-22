int main1(int o,int p){
  int ojx, e1, bu, y6f, bx;
  ojx=o+13;
  e1=0;
  bu=0;
  y6f=(o%28)+10;
  bx=e1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= bu;
  loop invariant bx == e1 + bu*(ojx - e1);
  loop invariant y6f == (o % 28) + 10 - bu*(bu - 1)/2;
  loop invariant e1 == 0;
  loop invariant ojx == o + 13;
  loop invariant y6f + (bu*(bu - 1))/2 == ((\at(o, Pre) % 28) + 10);
  loop assigns bu, y6f, bx;
*/
while (y6f>bu) {
      y6f = y6f - bu;
      bx = bx+ojx-e1;
      bu += 1;
  }
}