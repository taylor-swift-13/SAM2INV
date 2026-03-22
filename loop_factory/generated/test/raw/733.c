int main1(int a){
  int cs, yq, kmzf;

  cs=0;
  yq=(a%28)+10;
  kmzf=0;

  while (yq>cs) {
      yq -= cs;
      kmzf += yq;
      cs++;
  }

}
