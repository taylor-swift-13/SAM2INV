int main1(int b,int q){
  int l, i, s;

  l=39;
  i=3;
  s=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*(s + 3) == i*(i + 1) && 3 <= i && i <= l;
  loop invariant b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant i >= 3;
  loop invariant i <= l;
  loop invariant 2*(s - 3) == i * i + i - 12;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 2*s == i*(i+1) - 6;
  loop invariant 3 <= i && i <= l;
  loop invariant l == 39;
  loop invariant 2*(s - 3) == (i - 3)*(i + 4);
  loop invariant 3 <= i && i <= l && b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant 2*s == i*i + i - 6;
  loop invariant 2*s == i*i + i - 6 && i >= 3 && i <= l;
  loop invariant b == \at(b, Pre) && q == \at(q, Pre) && l == 39;
  loop invariant s == i*(i+1)/2 - 3;
  loop invariant i >= 3 && i <= l && b == \at(b, Pre) && q == \at(q, Pre);
  loop assigns s, i;
*/
while (i<=l-1) {
      s = s+1;
      s = s+i;
      i = i+1;
  }

}
