int main1(int q){
  int i, j, w, s;

  i=19;
  j=i;
  w=i;
  s=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j - 4*s == -57);
  loop invariant (w + s == 38);
  loop invariant (i == 19);
  loop invariant (q == \at(q, Pre));
  loop invariant (s <= 19);
  loop invariant (j <= 19);
  loop invariant (w >= 19);
  loop invariant i == 19;
  loop invariant q == \at(q, Pre);
  loop invariant s + w == 38;
  loop invariant j == 95 - 4*w;
  loop invariant j >= 3;
  loop invariant 3 <= j;
  loop invariant j <= 19;
  loop invariant w >= 19;
  loop assigns w, s, j;
*/
while (j>3) {
      w = w+1;
      s = s-1;
      j = j-4;
  }

}
