int main1(int t){
  int yh, vf4, mz, s, qey, qc1;

  yh=(t%10)+11;
  vf4=yh;
  mz=t;
  s=vf4;
  qey=16;
  qc1=(t%35)+8;

  while (qc1>0) {
      mz = mz+s*s;
      qey = qey+qc1*qc1;
      s = s+qc1*qc1;
      qc1--;
      t += vf4;
  }

}
