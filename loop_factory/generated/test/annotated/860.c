int main1(int f){
  int db, v3, bd, u0;
  db=f+22;
  v3=db;
  bd=0;
  u0=db;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v3 == u0;
  loop invariant (db == f + 22);
  loop invariant (bd <= u0*u0);
  loop invariant v3 >= \at(f, Pre) + 22;
  loop invariant 0 <= bd;
  loop assigns u0, bd, v3;
*/
while (v3-1>=0) {
      u0 = u0 + 1;
      bd = u0*u0;
      v3++;
  }
}