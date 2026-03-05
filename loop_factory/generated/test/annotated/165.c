int main1(int n){
  int vd, mql;
  vd=n;
  mql=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= mql <= 1;
  loop invariant n == \at(n, Pre) + (1 - mql) * vd;
  loop invariant vd == \at(n, Pre);
  loop assigns mql, n;
*/
while (mql!=mql) {
      if (mql>mql) {
          mql -= mql;
          mql -= mql;
          mql -= mql;
      }
      else {
          mql -= mql;
          mql -= mql;
          mql -= mql;
      }
      n += vd;
  }
}