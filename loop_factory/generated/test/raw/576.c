int main1(int v,int g){
  int ny, d, hti, ys, pq;

  ny=8;
  d=1;
  hti=0;
  ys=0;
  pq=11;

  while (d<=ny) {
      d = 2*d;
      hti++;
      pq = pq*3+(d%4)+0;
      ys = ys*4+(d%6)+3;
  }

}
