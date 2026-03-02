int main1(int m,int p){
  int l, j, v;

  l=m;
  j=0;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(m, Pre) && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant l == \at(m, Pre) && p == \at(p, Pre) && j >= 0 && 0 <= v && v <= 5;
  loop invariant (j == 0 && v == 0) || ((j - v) % 6 == 1);
  loop invariant (((j==0 && v==0) || ((j - v) % 6 == 1)) && 0 <= v && v <= 5 && j >= 0);
  loop invariant (l == \at(m, Pre) && m == \at(m, Pre) && p == \at(p, Pre));
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant l == m;
  loop invariant j >= 0;
  loop invariant 0 <= v && v <= 5;
  loop invariant j == 0 ==> v == 0;
  loop invariant j > 0 ==> v == (j - 1) % 6;
  loop invariant l == \at(m, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant l == \at(m, Pre) && p == \at(p, Pre);
  loop invariant j >= 0 && 0 <= v && v <= 5;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && l == \at(m, Pre);
  loop assigns j, v;
*/
while (1) {
      if ((j%6)==0) {
          v = v-v;
      }
      else {
          v = v+1;
      }
      j = j+1;
  }

}
