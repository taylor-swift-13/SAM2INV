int main1(int b,int m){
  int j, i, c, k;

  j=m;
  i=3;
  c=m;
  k=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == m;
  loop invariant i >= 3;

  loop invariant c >= m;
  loop invariant 2*c == 2*m + i*i + 21*i - 72;
  loop invariant j == \at(m, Pre);
  loop invariant c >= \at(m, Pre);
  loop invariant k >= 3;
  loop invariant c - i >= m - 3;
  loop invariant (j == m) &&
                   (i >= 3) &&
                   (c >= m) &&
                   (k >= 3) &&
                   (b == \at(b, Pre)) &&
                   (m == \at(m, Pre));
  loop invariant c == \at(m, Pre) + 14*(i - 3) + ((i - 3)*(i - 4))/2;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns c, i, k;
*/
while (1) {
      if (i>=j) {
          break;
      }
      c = c+3;
      i = i+1;
      k = k+k;
      k = k+c;
      if (j<j+4) {
          c = c+1;
      }
      c = c+6;
      k = k+c;
      c = c+i;
  }

}
