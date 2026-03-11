int main1(int k,int q){
  int j, v, t;

  j=(k%18)+18;
  v=0;
  t=k;


while (v<j) {
      t = t+v;
      v = v+1;
  }
/*@
  assert !(v<j) &&
         (t == k + (v*(v-1))/2);
*/

}
