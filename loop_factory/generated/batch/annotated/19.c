int main1(int k,int m){
  int f, j, o;

  f=m-3;
  j=0;
  o=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(m, Pre) - 3;
  loop invariant o == 6 + 4 * ((j + 8) / 9);
  loop invariant j >= 0;

  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= j && (j <= f || j == 0) && f == \at(m, Pre) - 3 && m == \at(m, Pre) && k == \at(k, Pre);
  loop invariant f == m - 3;
  loop invariant 0 <= j;

  loop assigns o, j;
*/
while (j<f) {
      if ((j%9)==0) {
          o = o+4;
      }
      j = j+1;
  }

}
