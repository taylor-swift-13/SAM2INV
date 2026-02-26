int main1(int a,int b){
  int i, k, l;

  i=(a%27)+13;
  k=0;
  l=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(a, Pre) % 27 + 13;
  loop invariant k == 0;
  loop invariant l == -2 || l == 2;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant i == (a % 27) + 13;
  loop invariant -2 <= l;
  loop invariant l <= 2;
  loop invariant i == (\at(a, Pre) % 27) + 13;

  loop invariant i == ((\at(a, Pre) % 27) + 13);
  loop invariant (l == -2) || (l == 2);
  loop assigns l;
*/
while (k+1<=i) {
      l = l+4;
      l = l%4;
  }

}
