int main1(int t,int e){
  int ll, y, lu, cotj;

  ll=e*3;
  y=0;
  lu=0;
  cotj=0;

  while (1) {
      if (!(cotj<=ll-1)) {
          break;
      }
      cotj = cotj + 1;
      t = t + y;
      lu = (lu+1)%3;
      t += 1;
  }

}
