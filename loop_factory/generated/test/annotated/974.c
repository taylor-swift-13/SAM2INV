int main1(int p,int x){
  int uo0, d, k2t, cnk;
  uo0=79;
  d=5;
  k2t=0;
  cnk=uo0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k2t >= 0;
  loop invariant cnk >= 0;
  loop invariant k2t <= uo0;
  loop invariant k2t + cnk == uo0;
  loop invariant p == \at(p,Pre) + k2t*(d+1);
  loop assigns cnk, p, k2t;
*/
while (k2t<uo0&&cnk>0) {
      cnk -= 1;
      p += d;
      k2t = (1)+(k2t);
      p++;
  }
}