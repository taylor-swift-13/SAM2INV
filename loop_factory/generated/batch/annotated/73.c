int main1(int a,int b){
  int i, k, l;

  i=(a%27)+13;
  k=0;
  l=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= k;
  loop invariant (k == 0 && l == -8) || l == a - 6;
  loop invariant k == 0 || k <= i;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant i == (\at(a, Pre) % 27) + 13;
  loop invariant ((l == -8) || (l == a - 6)) && (0 <= k);

  loop invariant (k==0 ==> l == -8) && (k>0 ==> l == a-6);
  loop invariant i == \at(a, Pre) % 27 + 13;
  loop invariant i == (a % 27) + 13;
  loop invariant (((k == 0) ==> (l == -8)) && ((k > 0) ==> (l == a - 6)) && (a == \at(a, Pre)) && (b == \at(b, Pre)) && (0 <= k));
  loop invariant k >= 0;
  loop invariant (k == 0 ==> l == -8) && (k >= 1 ==> l == a - 6);
  loop assigns k, l;
*/
while (k<i) {
      l = l+k;
      l = a-6;
      k = k+1;
  }

}
