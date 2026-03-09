int main1(int f,int h){
  int xu, dcdv, oj, q;

  xu=64;
  dcdv=0;
  oj=dcdv;
  q=5;

  while (1) {
      if (!(oj<xu)) {
          break;
      }
      oj++;
      q = q + oj;
      f += 2;
      h = h + oj;
  }

}
