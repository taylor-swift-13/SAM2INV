int main1(int e,int y){
  int s, od, wpl;

  s=(y%14)+5;
  od=s;
  wpl=-3;

  while (od>=3) {
      wpl = wpl + wpl;
      e = e + wpl;
  }

}
