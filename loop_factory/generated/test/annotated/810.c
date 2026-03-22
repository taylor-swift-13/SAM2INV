int main1(int f,int m){
  int e2, mct, v1u;
  e2=16;
  mct=0;
  v1u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v1u <= e2;
  loop invariant mct == v1u * f;
  loop invariant v1u >= 0;
  loop assigns v1u, mct;
*/
while (1) {
      if (!(v1u<e2)) {
          break;
      }
      v1u += 1;
      mct += f;
  }
}