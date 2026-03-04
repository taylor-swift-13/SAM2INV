int main1(int v){
  int t, pyiz;

  t=0;
  pyiz=(v%15)+3;

  while (pyiz!=0) {
      pyiz -= 1;
      v += t;
  }

}
