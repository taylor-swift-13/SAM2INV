int main13(int l,int r){
  int qj, ndz6, mf, au, wvji;

  qj=0;
  ndz6=(l%20)+10;
  mf=(l%15)+8;
  au=5;
  wvji=0;

  while (ndz6>0&&mf>0) {
      if (qj%2==0) {
          ndz6 = ndz6 - 1;
      }
      else {
          mf -= 1;
      }
      qj = qj + 1;
      r = r + 3;
      wvji += ndz6;
      au += wvji;
  }

}
