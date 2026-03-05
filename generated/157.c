int main157(int c,int o){
  int i81, m, sz9, qy, wf, sq;

  i81=c*2;
  m=0;
  sz9=1;
  qy=6;
  wf=c;
  sq=7;

  while (m<i81) {
      qy = qy + 5;
      m++;
      sz9 = sz9 + 5;
      c = (c+sz9)%7;
      wf += 1;
      sq = sq + wf;
  }

}
