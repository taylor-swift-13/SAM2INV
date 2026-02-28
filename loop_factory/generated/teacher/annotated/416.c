int main1(int a,int k){
  int b, j, s, c;

  b=21;
  j=b;
  s=j;
  c=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j >= 0);
  loop invariant (j <= 21);
  loop invariant (s >= 0);
  loop invariant (s <= 462);
  loop invariant (a == \at(a, Pre));
  loop invariant (k == \at(k, Pre));
  loop invariant j >= 0;
  loop invariant j <= b;
  loop invariant s >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j <= 21;
  loop invariant s == 21 || (s >= 0 && s <= 5);
  loop invariant b == 21;
  loop invariant (s == 21) || (0 <= s && s <= 5);
  loop invariant (0 <= j && j <= 21);

  loop assigns s, j;
*/
while (j>0) {
      s = s*s+s;
      s = s%6;
      j = j/2;
  }

}
