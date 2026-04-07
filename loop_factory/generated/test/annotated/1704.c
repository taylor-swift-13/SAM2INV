int main1(){
  int xu, j9, aj, j9xo, r;
  xu=1*3;
  j9=xu;
  aj=0;
  j9xo=j9;
  r=j9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == xu * aj + 3;
  loop invariant 0 <= aj <= xu;
  loop invariant j9xo <= r;
  loop invariant r == xu * (aj + 1);
  loop invariant j9xo == xu;
  loop invariant (r - j9xo) % xu == 0;
  loop assigns aj, j9xo, r;
*/
while (aj<xu) {
      aj += 1;
      if (!(!(r<=j9xo))) {
          j9xo = r;
      }
      r = r + xu;
  }
}