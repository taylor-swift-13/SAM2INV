int main1(int o,int e){
  int tz, wq, q, dzs;

  tz=40;
  wq=0;
  q=1;
  dzs=1;

  while (q<=tz) {
      dzs += 2;
      wq++;
      q = q + dzs;
      o = o+(wq%3);
  }

}
