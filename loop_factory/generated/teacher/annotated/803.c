int main1(int a,int k){
  int g, w, i;

  g=(a%26)+19;
  w=0;
  i=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant w == 0;
  loop invariant g == (\at(a,Pre) % 26) + 19;
  loop invariant i >= k;

  loop invariant g == ((\at(a,Pre) % 26) + 19);

  loop invariant (i - k) % 2 == 0;
  loop invariant g == (a % 26) + 19;
  loop invariant ((i - k) % 2) == 0;
  loop assigns i;
*/
while (1) {
      i = i+3;
      i = i+1;
      if (g<w+5) {
          i = i+6;
      }
  }

}
