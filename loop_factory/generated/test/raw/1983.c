int main1(int x){
  int w6, gh, t22s;

  w6=x;
  gh=0;
  t22s=0;

  while (gh < w6) {
      gh = gh + 1;
      t22s = 1 - t22s;
      x = x+(gh%2);
      x -= x;
  }

}
