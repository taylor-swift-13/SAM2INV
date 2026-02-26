int main1(int a,int k){
  int b, j, s, c;

  b=21;
  j=b;
  s=j;
  c=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((s == 21 && c == a) || (s > 21 && c == s - 1));
  loop invariant j == 21;
  loop invariant s >= 21;
  loop invariant b == 21;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (s == 21 && c == a) || (s >= 22 && c == s - 1);
  loop invariant s >= j;
  loop invariant j >= 3;
  loop invariant (c == \at(a, Pre) && s == 21) || (c == s - 1 && s >= 22);
  loop assigns c, s;
*/
while (j>3) {
      c = s;
      s = s+1;
  }

}
