int main1(int t){
  int yh, vf4, mz, s, qey, qc1;
  yh=(t%10)+11;
  vf4=yh;
  mz=t;
  s=vf4;
  qey=16;
  qc1=(t%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= vf4;
  loop invariant qey >= 16;
  loop invariant mz >= \at(t,Pre);
  loop invariant (qey - s == 16 - vf4);
  loop invariant t >= \at(t, Pre);
  loop invariant s >= 0;
  loop invariant t - \at(t, Pre) == vf4 * ( ((\at(t, Pre) % 35) + 8) - qc1 );
  loop assigns mz, qey, s, qc1, t;
*/
while (qc1>0) {
      mz = mz+s*s;
      qey = qey+qc1*qc1;
      s = s+qc1*qc1;
      qc1--;
      t += vf4;
  }
}