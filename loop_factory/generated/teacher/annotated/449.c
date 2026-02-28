int main1(int a,int k){
  int r, l, o, j;

  r=(a%40)+5;
  l=0;
  o=-8;
  j=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant o >= -8;
  loop invariant ((o + 8) % 6) == 0;
  loop invariant j == r + ((o + 8) * (o + 8)) / 12 - (o + 8);
  loop invariant (o + 8) % 6 == 0;

  loop invariant r == (a % 40) + 5;
  loop invariant (j - r) % 3 == 0;


  loop assigns o, j;
*/
while (1) {
      o = o+4;
      o = o+1;
      j = j+o;
      o = o+1;
  }

}
